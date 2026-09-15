#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
kd2_merge.py — слияние файлов правил КД2 («Конвертация данных 2») по сущностям.

Проблема, которую он решает
--------------------------
Файл правил КД2 содержит многострочные текстовые узлы (код 1С внутри <Текст>,
<ПослеЗагрузки>, <ПередВыгрузкойДанных>...). Линейный diff (git/BC/kdiff3)
выравнивает строку N одного правила против строки N другого правила, из-за чего
сравниваются ДВЕ РАЗНЫЕ сущности — «мясорубка».

Здесь сравнение разного между собой невозможно по построению: файл разбирается на
элементы с точными диапазонами строк, и каждое решение принимается отдельно для
каждой сущности (Группа / Правило / Свойства / Свойство / Значения / Значение /
Алгоритм / Параметр / Обработка) и отдельно для каждого её поля.

Роли файлов
-----------
  --develop   актуальная версия из git — она является ОСНОВОЙ результата
  --mine      ваш файл (ветка + ваши правки) — отсюда берутся ВАШИ изменения
  --ancestor  необязательный общий предок (git merge-base) — включает честный 3-way

Правила разрешения
------------------
  сущность/поле идентичны (с точностью до пробелов) ......... остаётся develop
  меняли только вы (ancestor = develop) ..................... берётся ваша версия
  меняли только в develop (ancestor = вы) ................... остаётся develop
  текст: ваша версия = develop + добавленные строки ......... применяется автоматически
  текст: меняли обе стороны ................................. ТРЕБУЕТ РЕШЕНИЯ (остаётся develop)
  сущность есть только у вас ...................... вставляется (проверьте, что она ваша)
  сущность есть только в develop .................. остаётся
  метаданные файла (Ид, Наименование, ДатаВремяСоздания) ..... всегда из develop

Команды
-------
  python kd2_merge.py analyze [--develop D.xml] [--mine M.xml] [--ancestor O.xml]
  python kd2_merge.py merge   --out merged.xml [--decisions decisions.txt]
  python kd2_merge.py conflicts

Команда analyze ничего не пишет, кроме отчёта merge_report.md и шаблона решений
decisions.txt. Для спорных блоков в decisions.txt раскомментируйте строку
«ID = mine», после чего запустите merge — спорный блок возьмётся из вашего файла.
"""

import argparse
import difflib
import hashlib
import os
import re
import sys
from collections import defaultdict
from xml.parsers import expat

# Элементы, у которых есть собственные имя/идентичность: сопоставляются между
# файлами по идентичности, а не по номеру строки.
UNIT_TAGS = {"Группа", "Правило", "Свойство", "Значение", "Алгоритм",
             "Обработка", "Параметр", "Запрос", "ЭлементОтбора", "НаборОтборов"}

# Поля, по которым берётся идентичность сущности (в порядке приоритета).
# ВАЖНО: Наименование идёт раньше Код — у Свойство/Значение Код это авто-нумерация
# КД2, которая меняется при каждом экспорте файла (144 в develop и 6 у вас — это
# ОДНО И ТО ЖЕ свойство). Orientироваться на неё нельзя.
ID_CHILD_TAGS = ("Наименование", "Источник", "Приемник", "Код")
ID_ATTRS = ("Имя", "Наименование", "Name")

# Поля, которые не сравниваем вообще: авто-нумерация КД2.
AUTO_NUMBERED = {("Свойство", "Код"), ("Значение", "Код")}

# Метаданные самого файла правил — их не переносим никогда.
ROOT_META_TAGS = {"Ид", "Наименование", "ДатаВремяСоздания", "ВерсияФормата"}

STATUS_ORDER = ["need", "mine", "mine_add", "insert", "develop", "meta", "ws", "auto"]
STATUS_TEXT = {
    "need": "ТРЕБУЕТ РЕШЕНИЯ (меняли обе стороны)",
    "mine": "взято моё (в develop это место не менялось)",
    "mine_add": "взято моё (мои строки добавлены к версии develop)",
    "insert": "вставлена сущность, которой нет в develop",
    "develop": "осталось из develop (меняли только там)",
    "meta": "метаданные файла — всегда из develop",
    "ws": "разница только в пробелах/переводах строк",
    "auto": "техническое поле КД2 (Код/Порядок) — оставлено из develop, не является правкой",
}

# Технические поля КД2, которые пересчитываются при каждом экспорте файла:
# авто-нумерация свойств/значений и позиция в списке. Отличие в них — не правка.
# (тег родителя, тег поля) -> всегда остаётся версия develop.
AUTO_NUMBERED_FIELDS = {
    ("Свойство", "Код"), ("Значение", "Код"),
    ("Свойство", "Порядок"), ("Значение", "Порядок"),
    ("Правило", "Порядок"), ("Группа", "Порядок"),
}


def is_technical_field(parent, child):
    """True, если поле child внутри parent — техническая авто-нумерация КД2.

    У вложенных Группа (табличные части: КонтактнаяИнформация и т.п.) <Код> —
    число, пересчитываемое при экспорте. У верхних Группа <Код> = «Справочники» —
    осмысленное имя, его не трогаем.
    """
    if (parent.tag, child.tag) in AUTO_NUMBERED_FIELDS:
        return True
    if parent.tag == "Группа" and child.tag == "Код":
        value = collapse(child.text())
        return bool(value) and value.isdigit()
    return False


# --------------------------------------------------------------------- разбор

class Node:
    __slots__ = ("tag", "attrs", "start", "end", "children", "texts", "parent")

    def __init__(self, tag, attrs, start):
        self.tag = tag
        self.attrs = attrs
        self.start = start
        self.end = start
        self.parent = None
        self.children = []
        self.texts = []

    def text(self):
        return "".join(self.texts)

    def child_text(self, tag):
        for c in self.children:
            if c.tag == tag and not c.children:
                return collapse(c.text())
        return None

    def kind(self):
        if self.children:
            return "container"
        return "text" if self.text().strip() else "empty"


def collapse(value):
    return " ".join((value or "").split())


def parse_doc(path):
    with open(path, "rb") as handle:
        raw = handle.read()
    body = raw[3:] if raw.startswith(b"\xef\xbb\xbf") else raw
    doc = Doc()
    doc.path = path
    doc.bom = raw.startswith(b"\xef\xbb\xbf")
    doc.eol = "\r\n" if b"\r\n" in body[:20000] else "\n"
    doc.lines = body.decode("utf-8", "replace").replace("\r\n", "\n").replace("\r", "\n").split("\n")

    parser = expat.ParserCreate()
    stack = []
    root = [None]

    def start_tag(tag, attrs):
        node = Node(tag, dict(attrs), parser.CurrentLineNumber)
        if stack:
            node.parent = stack[-1]
            stack[-1].children.append(node)
        else:
            root[0] = node
        stack.append(node)

    def end_tag(_tag):
        stack.pop().end = parser.CurrentLineNumber

    def chars(data):
        if stack:
            stack[-1].texts.append(data)

    parser.StartElementHandler = start_tag
    parser.EndElementHandler = end_tag
    parser.CharacterDataHandler = chars
    try:
        parser.Parse(body, True)
    except expat.ExpatError as exc:
        raise SystemExit("Не удалось разобрать %s: %s" % (path, exc))
    doc.root = root[0]
    return doc


class Doc:
    def block(self, node):
        return "\n".join(self.lines[node.start - 1:node.end])

    def block_lines(self, node):
        return self.lines[node.start - 1:node.end]


# ---------------------------------------------------------------- идентичность

def identity(node):
    """Идентичность сущности: атрибут Имя/Наименование, иначе Код/Источник/Приемник."""
    if node.tag not in UNIT_TAGS:
        return None
    for attr in ID_ATTRS:
        value = collapse(node.attrs.get(attr))
        if value:
            return ("A", value)
    for tag in ID_CHILD_TAGS:
        value = node.child_text(tag)
        if value:
            return (tag, value)
    return None


def child_key(node, occurrence):
    ident = identity(node)
    if ident is None:
        return (node.tag, "T", occurrence)
    return (node.tag, ident[0], ident[1])


def key_map(children):
    """Список ключей детей (позиционные ключи нумеруются) и словарь ключ -> узел."""
    counts = defaultdict(int)
    keys, result = [], {}
    for child in children:
        base = child_key(child, 0)
        if base[1] == "T":
            occurrence = counts[base]
            counts[base] += 1
            key = child_key(child, occurrence)
        else:
            key = base
        keys.append(key)
        result.setdefault(key, child)
    return keys, result


def unit_label(node):
    ident = identity(node)
    if ident is None:
        return node.tag
    value = ident[1]
    return "%s[%s]" % (node.tag, value if len(value) <= 70 else value[:67] + "...")


def node_id(path):
    return hashlib.md5(path.encode("utf-8")).hexdigest()[:8]


# ------------------------------------------------------------- сопоставление

def signature(node, _cache={}):
    """Дешевая «подпись» содержимого: все тексты поддерева одной строкой."""
    key = id(node)
    cached = _cache.get(key)
    if cached is not None:
        return cached
    parts = [collapse(node.text())]
    for child in node.children:
        parts.append(signature(child, _cache))
    value = " ".join(p for p in parts if p)[:4000]
    _cache[key] = value
    return value


def similar(a, b):
    """Похожи ли два блока (переименованная сущность), а не две разные сущности."""
    if a.tag != b.tag:
        return 0.0
    ta = signature(a) or re.sub(r"\s+", "", str(a.attrs))[:400]
    tb = signature(b) or re.sub(r"\s+", "", str(b.attrs))[:400]
    if not ta or not tb:
        return 0.0
    quick = difflib.SequenceMatcher(None, ta, tb)
    if quick.real_quick_ratio() < 0.6 or quick.quick_ratio() < 0.6:
        return 0.0
    return quick.ratio()


def align_children(children_a, children_b, fuzzy_threshold=0.85):
    """[(kind, a|None, b|None)]. kind: 'both' | 'a' (только develop) | 'b' (только мои).

    Сначала точное совпадение идентичности; одноимённые подбираются по сходству
    содержимого. Остатки сопоставляются нечётко ТОЛЬКО если очень похожи —
    иначе это две разные сущности, и они идут в add/remove, а не в diff.
    """
    keys_a, _ = key_map(children_a)
    keys_b, _ = key_map(children_b)
    bucket_a, bucket_b = defaultdict(list), defaultdict(list)
    for key, node in zip(keys_a, children_a):
        bucket_a[key].append(node)
    for key, node in zip(keys_b, children_b):
        bucket_b[key].append(node)

    pairs, used_a, used_b = [], set(), set()
    for key in set(bucket_a) & set(bucket_b):
        group_a, group_b = bucket_a[key], bucket_b[key]
        if len(group_a) == 1 and len(group_b) == 1:
            pairs.append((group_a[0], group_b[0]))
            used_a.add(id(group_a[0]))
            used_b.add(id(group_b[0]))
            continue
        scored = sorted(((similar(a, b), a, b) for a in group_a for b in group_b),
                        key=lambda item: -item[0])
        for _ratio, a, b in scored:
            if id(a) in used_a or id(b) in used_b:
                continue
            pairs.append((a, b))
            used_a.add(id(a))
            used_b.add(id(b))

    rest_a = [n for n in children_a if id(n) not in used_a]
    rest_b = [n for n in children_b if id(n) not in used_b]
    if len(rest_a) * len(rest_b) <= 40000:
        by_tag = defaultdict(list)
        for b in rest_b:
            by_tag[b.tag].append(b)
        scored = []
        for a in rest_a:
            for b in by_tag.get(a.tag, ()):
                ratio = similar(a, b)
                if ratio >= fuzzy_threshold:
                    scored.append((ratio, a, b))
        for ratio, a, b in sorted(scored, key=lambda item: -item[0]):
            if id(a) in used_a or id(b) in used_b:
                continue
            pairs.append((a, b))
            used_a.add(id(a))
            used_b.add(id(b))

    ops = [("both", a, b) for a, b in pairs]
    ops += [("a", a, None) for a in children_a if id(a) not in used_a]
    ops += [("b", None, b) for b in children_b if id(b) not in used_b]

    def position(op):
        node = op[1] or op[2]
        return (node.parent.children.index(node), node.start)

    ops.sort(key=position)
    return ops


def is_pure_addition(a_lines, b_lines):
    """b = a + добавленные строки: ни одной удалённой или изменённой строки из a."""
    if not [l for l in a_lines if l.strip()]:
        return False
    inserted = False
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a_lines, b_lines,
                                                       autojunk=False).get_opcodes():
        if tag == "insert":
            inserted = True
        elif tag != "equal":
            return False
    return inserted


# ------------------------------------------------------------------- слияние

class Item:
    def __init__(self, status, path, node_a, node_b, note=""):
        self.status = status
        self.path = path
        self.id = node_id(path)
        self.note = note
        self.a = node_a
        self.b = node_b
        self.resolved = None


class Merger:
    def __init__(self, develop, mine, ancestor=None, decisions=None, prefer_mine=False):
        self.dev = develop
        self.mine = mine
        self.anc = ancestor
        self.decisions = decisions or {}
        self.prefer_mine = prefer_mine
        self.edits = []
        self.items = []
        self.counts = defaultdict(int)

    # --- вывод ---
    def _replace(self, node_a, node_b):
        self.edits.append({"op": "replace", "start": node_a.start,
                           "end": node_a.end, "lines": self.mine.block_lines(node_b)})

    def _insert_after(self, line, node_b):
        self.edits.append({"op": "insert_after", "line": line,
                           "lines": self.mine.block_lines(node_b)})

    def _delete(self, node_a):
        self.edits.append({"op": "delete", "start": node_a.start, "end": node_a.end})

    def _item(self, status, path, node_a, node_b, note=""):
        item = Item(status, path, node_a, node_b, note)
        self.items.append(item)
        self.counts[status] += 1
        return item

    def _decided(self, path, item):
        value = self.decisions.get(item.id) or self.decisions.get(path)
        if value in ("mine", "my", "branch"):
            return "mine"
        if value in ("develop", "theirs", "keep"):
            return "develop"
        return None

    # --- рекурсия ---
    def merge_pair(self, a, b, anc, path):
        kind_a, kind_b = a.kind(), b.kind()
        if norm_equal(self.dev.block(a), self.mine.block(b)):
            if self.dev.block(a) != self.mine.block(b):
                self._item("ws", path, a, b)
            return
        if kind_a == "container" and kind_b == "container":
            self.merge_children(a, b, anc, path)
            return
        if kind_a == "text" and kind_b == "text":
            self.merge_text(a, b, anc, path)
            return
        if kind_a == "empty" and kind_b == "container":
            item = self._item("insert", path, a, b,
                              "в develop блок пуст, у вас наполнен — взято ваше содержимое")
            item.resolved = "mine"
            self._replace(a, b)
            return
        if kind_a == "container" and kind_b == "empty":
            self._item("develop", path, a, b,
                       "у вас блок пуст — наполнение из develop сохранено")
            return
        self.merge_structural(a, b, anc, path)

    def merge_text(self, a, b, anc, path):
        a_lines = [l.strip() for l in self.dev.block(a).split("\n")]
        b_lines = [l.strip() for l in self.mine.block(b).split("\n")]
        if anc is not None:
            base = [l.strip() for l in self.anc.block(anc).split("\n")]
            mine_changed = norm_equal(self.mine.block(b), self.anc.block(anc)) is False
            dev_changed = norm_equal(self.dev.block(a), self.anc.block(anc)) is False
            if dev_changed and not mine_changed:
                self._item("develop", path, a, b, "меняли только в develop")
                return
            if mine_changed and not dev_changed:
                item = self._item("mine", path, a, b, "в develop это место не менялось")
                item.resolved = "mine"
                self._replace(a, b)
                return
            if not mine_changed and not dev_changed:
                self._item("ws", path, a, b)
                return
        else:
            base = None

        if is_pure_addition(a_lines, b_lines):
            item = self._item("mine_add", path, a, b,
                              "ваши строки добавлены к тексту develop, ничего из develop не удаляется")
            item.resolved = "mine"
            self._replace(a, b)
            return
        if base is not None and is_pure_addition(base, a_lines):
            self._item("develop", path, a, b, "develop дописал строки, у вас этот блок не менялся")
            return

        item = self._item("need", path, a, b,
                          "изменения и у вас, и в develop; в результате пока версия develop")
        if self.prefer_mine or self._decided(path, item) == "mine":
            item.resolved = "mine"
            self._replace(a, b)
        else:
            item.resolved = "develop (по умолчанию)"

    def merge_structural(self, a, b, anc, path):
        """Разница в атрибутах/вложенности при несовпадимой структуре блока."""
        item = self._item("need", path, a, b,
                          "различается структура/атрибуты блока (%s → %s)" % (a.kind(), b.kind()))
        if self.prefer_mine or self._decided(path, item) == "mine":
            item.resolved = "mine"
            self._replace(a, b)
        else:
            item.resolved = "develop (по умолчанию)"

    def merge_children(self, a, b, anc, path):
        anc_children = anc.children if anc is not None else []
        anc_keys = {}
        if anc_children:
            _, anc_keys = key_map(anc_children)

        def take_ancestor(node):
            key = child_key(node, 0)
            return anc_keys.pop(key) if key in anc_keys else None

        anchor = a.start
        for kind, child_a, child_b in align_children(a.children, b.children):
            child_path = path + "/" + unit_label(child_a or child_b)
            field_tag = (child_a or child_b).tag
            technical = is_technical_field(a, child_a or child_b)
            if kind == "both":
                if technical:
                    if not norm_equal(self.dev.block(child_a), self.mine.block(child_b)):
                        self._item("auto", child_path, child_a, child_b,
                                   "техническое поле КД2 (Код/Порядок) — оставлена версия develop")
                    anchor = child_a.end
                    continue
                self.merge_pair(child_a, child_b, take_ancestor(child_a), child_path)
                anchor = child_a.end
            elif child_a is not None:
                if technical:
                    self._item("auto", child_path, child_a, None,
                               "техническое поле КД2 есть только в develop — оставлено")
                    anchor = child_a.end
                    continue
                if self.anc is not None and take_ancestor(child_a) is not None:
                    item = self._item("need", child_path, child_a, None,
                                      "вы эту сущность удалили, в develop она есть — пока осталась")
                    if self.prefer_mine or self._decided(child_path, item) == "mine":
                        item.resolved = "удалена (как у вас)"
                        self._delete(child_a)
                    else:
                        item.resolved = "develop (по умолчанию)"
                else:
                    self._item("develop", child_path, child_a, None,
                               "сущность есть только в develop")
                anchor = child_a.end
            else:
                if technical:
                    self._item("auto", child_path, None, child_b,
                               "техническое поле КД2 есть только у вас — не переносится")
                    continue
                if self.anc is not None and find_by_tag_or_identity(anc_children, child_b):
                    self._item("develop", child_path, None, child_b,
                               "в предке была, в develop удалена — оставили удалённой")
                    continue
                item = self._item("insert", child_path, None, child_b,
                                  "в develop такой сущности нет — вставлена ваша версия")
                item.resolved = "insert"
                self._insert_after(anchor, child_b)

    def run(self):
        root_a, root_b = self.dev.root, self.mine.root
        if root_a.tag != root_b.tag:
            raise SystemExit("Разные корневые элементы: %s и %s" % (root_a.tag, root_b.tag))
        anc_root = self.anc.root if self.anc is not None else None
        for child_a in root_a.children:
            path = "/" + unit_label(child_a)
            child_b = find_by_tag_or_identity(root_b.children, child_a)
            if child_b is None:
                self._item("develop", path, child_a, None, "есть только в develop")
                continue
            if child_a.tag in ROOT_META_TAGS:
                if not norm_equal(self.dev.block(child_a), self.mine.block(child_b)):
                    self._item("meta", path, child_a, child_b,
                               "это идентификатор/название файла правил — остаётся из develop")
                continue
            anc_child = find_by_tag_or_identity(anc_root.children, child_a) if anc_root else None
            self.merge_pair(child_a, child_b, anc_child, path)
        return self

    def render(self):
        replaces = {}
        deletes = {}
        inserts = defaultdict(list)
        for edit in self.edits:
            if edit["op"] == "replace":
                replaces[edit["start"]] = (edit["end"], edit["lines"])
            elif edit["op"] == "delete":
                deletes[edit["start"]] = edit["end"]
            else:
                inserts[edit["line"]].extend(edit["lines"])
        out = []
        lines = self.dev.lines
        i = 1
        while i <= len(lines):
            if i in deletes:
                end = deletes[i]
                for anchor in range(i, end + 1):
                    if anchor in inserts:
                        out.extend(inserts.pop(anchor))
                i = end + 1
                continue
            if i in replaces:
                end, new_lines = replaces[i]
                out.extend(new_lines)
                for anchor in range(i, end + 1):
                    if anchor in inserts:
                        out.extend(inserts.pop(anchor))
                i = end + 1
                continue
            out.append(lines[i - 1])
            if i in inserts:
                out.extend(inserts.pop(i))
            i += 1
        for anchor in sorted(inserts):
            out.extend(inserts[anchor])
        return out


def find_by_tag_or_identity(children, node):
    for child in children:
        if child.tag != node.tag:
            continue
        if identity(node) is None or identity(child) == identity(node):
            return child
    return None


def norm_equal(text_a, text_b):
    return re.sub(r"\s+", "", text_a) == re.sub(r"\s+", "", text_b)


# ------------------------------------------------------------------- отчёт

def diff_of(item, max_lines=80):
    if item.a is None:
        return ["+ сущность только в вашем файле (%d строк)" % len(item.b.raw_lines()
                if hasattr(item.b, "raw_lines") else [])]
    if item.b is None:
        return ["- сущность только в develop"]
    a = Merger.doc_block(item.a).split("\n")
    b = Merger.doc_block(item.b).split("\n")
    return a, b


def item_diff_lines(merger, item, max_lines=80):
    if item.a is None:
        body = merger.mine.block_lines(item.b)
        head = ["+ ваша сущность, в develop отсутствует (%d строк)" % len(body)]
        return head + body[:max_lines]
    if item.b is None:
        body = merger.dev.block_lines(item.a)
        return ["- сущность только в develop (%d строк), у вас её нет" % len(body)]
    a = merger.dev.block_lines(item.a)
    b = merger.mine.block_lines(item.b)
    if max(len(a), len(b)) > 3000:
        return ["(очень большой блок: %d → %d строк; дифф не выводится, смотрите построчно в редакторе)"
                % (len(a), len(b))]
    out = list(difflib.unified_diff(a, b,
                                    "develop, стр. %d" % item.a.start,
                                    "мой файл, стр. %d" % item.b.start,
                                    lineterm="", n=2))
    if len(out) > max_lines:
        out = out[:max_lines] + ["... ещё %d строк пропущено ..." % (len(out) - max_lines)]
    return out


def build_report(merger, out_path, decisions_path, result_path):
    groups = defaultdict(list)
    for item in merger.items:
        groups[item.status].append(item)

    L = ["# Слияние правил КД2: develop + мои изменения", ""]
    L.append("| роль | файл | строк |")
    L.append("|---|---|---|")
    L.append("| develop (основа результата) | `%s` | %d |" % (merger.dev.path, len(merger.dev.lines)))
    L.append("| мой файл (источник изменений) | `%s` | %d |" % (merger.mine.path, len(merger.mine.lines)))
    L.append("| предок (3-way) | %s | %s |" % (
        "`%s`" % merger.anc.path if merger.anc else "не задан — включена эвристика чистого добавления",
        len(merger.anc.lines) if merger.anc else "-"))
    if result_path:
        L.append("| результат | `%s` | — |" % result_path)
    L.append("")
    L.append("Сравнение разного между собой невозможно: блоки сопоставляются только по идентичности"
             " сущности (Код/Имя/Источник/Приемник), поэтому diff всегда остаётся внутри одного правила"
             " или одного свойства.")
    L.append("")
    L.append("## Сводка")
    L.append("")
    L.append("| статус | количество |")
    L.append("|---|---|")
    for status in STATUS_ORDER:
        if groups.get(status):
            L.append("| %s | **%d** |" % (STATUS_TEXT[status], len(groups[status])))
    L.append("")

    if groups.get("need"):
        L.append("## Требуют решения (%d)" % len(groups["need"]))
        L.append("")
        L.append("По умолчанию в результате — версия develop. Чтобы взять свою, раскомментируйте"
                 " строку в `%s` и перезапустите `merge`." % os.path.basename(decisions_path))
        L.append("")
        L.append("| ID | стр. develop | стр. мой | сущность |")
        L.append("|---|---|---|---|")
        for item in groups["need"]:
            L.append("| `%s` | %s | %s | %s |" % (
                item.id,
                "%d–%d" % (item.a.start, item.a.end) if item.a else "—",
                "%d–%d" % (item.b.start, item.b.end) if item.b else "—",
                item.path.replace("/", " / ")))
        L.append("")

    for status in STATUS_ORDER:
        items = groups.get(status) or []
        if not items:
            continue
        L.append("## %s (%d)" % (STATUS_TEXT[status], len(items)))
        L.append("")
        if status == "need":
            L.append("По умолчанию в результате остаётся версия develop. Если это ваша правка —"
                     " раскомментируйте строку `ID = mine` в `%s` и перезапустите merge."
                     % os.path.basename(decisions_path))
            L.append("")
        for item in items:
            L.append(render_item(merger, item))
    with open(out_path, "w", encoding="utf-8-sig") as handle:
        handle.write("\n".join(L) + "\n")

    with open(decisions_path, "w", encoding="utf-8") as handle:
        handle.write("# Спорные блоки: уберите '#' и поставьте '= mine', чтобы взять свою версию\n")
        handle.write("# Формат: <ID> = mine | develop\n")
        handle.write("# Затем: python kd2_merge.py merge --out merged.xml --decisions %s\n\n"
                     % os.path.basename(decisions_path))
        for item in groups.get("need", []):
            handle.write("# %s = mine   # %s\n" % (item.id, item.path.replace("/", " / ")))
    return groups


def render_item(merger, item):
    lines = ["### `%s` — %s" % (item.id, item.path.replace("/", " / ")), ""]
    where = []
    if item.a:
        where.append("develop: стр. %d–%d" % (item.a.start, item.a.end))
    if item.b:
        where.append("мой файл: стр. %d–%d" % (item.b.start, item.b.end))
    if where:
        lines.append("- " + " | ".join(where))
    if item.note:
        lines.append("- %s" % item.note)
    if item.resolved:
        lines.append("- в результате: `%s`" % item.resolved)
    lines.append("")
    body = item_diff_lines(merger, item)
    if body:
        lines.append("```diff")
        lines.extend(body)
        lines.append("```")
    lines.append("")
    return "\n".join(lines)


def write_output(path, lines, doc):
    data = doc.eol.join(lines).encode("utf-8")
    if doc.bom:
        data = b"\xef\xbb\xbf" + data
    with open(path, "wb") as handle:
        handle.write(data)


def load_decisions(path):
    decisions = {}
    if not path or not os.path.exists(path):
        return decisions
    with open(path, encoding="utf-8-sig") as handle:
        for raw in handle:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            if "=" not in line:
                continue
            key, value = line.split("=", 1)
            decisions[key.strip()] = value.strip().lower()
    return decisions


# ----------------------------------------------------------------------- CLI

def default_files():
    xmls = [f for f in os.listdir(".") if f.lower().endswith(".xml")]
    dev = [f for f in xmls if "develop" in f.lower()]
    mine = [f for f in xmls if "develop" not in f.lower()]
    if len(dev) == 1 and len(mine) == 1:
        return dev[0], mine[0]
    raise SystemExit("Укажите --develop и --mine явно (в папке: %s)" % ", ".join(xmls))


def build_merger(args):
    develop, mine = (args.develop, args.mine) if args.develop and args.mine else default_files()
    args.develop, args.mine = develop, mine
    ancestor = parse_doc(args.ancestor) if args.ancestor else None
    decisions = load_decisions(args.decisions)
    return Merger(parse_doc(develop), parse_doc(mine), ancestor,
                  decisions, args.prefer_mine).run()


def summary(merger):
    print("режим: %s" % ("3-way (есть предок)" if merger.anc else "2-way (эвристика чистого добавления)"))
    for status in STATUS_ORDER:
        if merger.counts.get(status):
            print("  %-9s %4d  %s" % (status, merger.counts[status], STATUS_TEXT[status]))


def main(argv=None):
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", nargs="?", default="analyze",
                        choices=["analyze", "merge", "conflicts"])
    parser.add_argument("--develop", help="актуальная версия из git (основа результата)")
    parser.add_argument("--mine", help="ваш файл с правками")
    parser.add_argument("--ancestor", help="общий предок (git merge-base) для честного 3-way")
    parser.add_argument("--out", help="файл результата для merge")
    parser.add_argument("--report", default="merge_report.md")
    parser.add_argument("--decisions", default="decisions.txt")
    parser.add_argument("--prefer-mine", action="store_true",
                        help="спорные блоки решать в пользу вашей версии")
    args = parser.parse_args(argv)

    if args.command == "conflicts":
        merger = build_merger(args)
        for item in merger.items:
            if item.status == "need":
                print("%s  develop:%d-%d  %s" % (item.id, item.a.start, item.a.end, item.path))
        print("спорных блоков: %d" % sum(1 for i in merger.items if i.status == "need"))
        return 0

    merger = build_merger(args)
    result = args.out if args.command == "merge" else None
    if result:
        if os.path.abspath(result) in (os.path.abspath(args.develop), os.path.abspath(args.mine)):
            raise SystemExit("--out не должен совпадать с исходными файлами")
        lines = merger.render()
        write_output(result, lines, merger.dev)
    groups = build_report(merger, args.report, args.decisions, result)
    summary(merger)
    print("отчёт: %s" % args.report)
    print("решения: %s (спорных: %d)" % (args.decisions, len(groups.get("need") or [])))
    if result:
        print("результат: %s" % result)
        print("проверка: git diff --no-index -- %s %s" % (args.develop, result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
