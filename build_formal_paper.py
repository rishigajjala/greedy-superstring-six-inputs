#!/usr/bin/env python3
"""Build the formal greedy-superstring manuscript as a polished PDF."""

from __future__ import annotations

import argparse
import html
import re
import textwrap
from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.pdfbase.pdfmetrics import stringWidth
from reportlab.platypus import (
    BaseDocTemplate,
    CondPageBreak,
    Frame,
    HRFlowable,
    KeepTogether,
    ListFlowable,
    ListItem,
    NextPageTemplate,
    PageBreak,
    PageTemplate,
    Paragraph,
    Preformatted,
    Spacer,
    Table,
    TableStyle,
)
from reportlab.platypus.tableofcontents import TableOfContents


ROOT = Path(__file__).resolve().parent
SOURCE = Path(__file__).resolve().with_name("FORMAL_PAPER.md")
DEFAULT_OUTPUT = ROOT / "output" / "pdf" / "greedy_shortest_superstring_at_most_six.pdf"

NAVY = colors.HexColor("#17324D")
BLUE = colors.HexColor("#285F8F")
TEAL = colors.HexColor("#0D7771")
INK = colors.HexColor("#202A33")
MUTED = colors.HexColor("#5D6974")
PALE_BLUE = colors.HexColor("#EEF5FA")
PALE_TEAL = colors.HexColor("#EDF8F6")
PALE_GRAY = colors.HexColor("#F5F7F9")
RULE = colors.HexColor("#CCD6DF")
WHITE = colors.white

PAGE_W, PAGE_H = A4
LEFT = 20 * mm
RIGHT = 20 * mm
TOP = 19 * mm
BOTTOM = 18 * mm
FRAME_W = PAGE_W - LEFT - RIGHT
FRAME_H = PAGE_H - TOP - BOTTOM


class FormalDocTemplate(BaseDocTemplate):
    def __init__(self, filename, metadata, **kwargs):
        self.metadata = metadata
        self._bookmark_counter = 0
        super().__init__(filename, pagesize=A4, **kwargs)
        frame = Frame(LEFT, BOTTOM, FRAME_W, FRAME_H, id="body")
        self.addPageTemplates(
            [
                PageTemplate(id="title", frames=[frame], onPage=self._title_page),
                PageTemplate(id="normal", frames=[frame], onPage=self._normal_page),
            ]
        )

    def _set_metadata(self, canvas):
        canvas.setTitle(self.metadata["title"])
        canvas.setSubject(self.metadata["subtitle"])
        canvas.setAuthor("Unauthored technical research artifact")
        canvas.setKeywords(
            "shortest common superstring, greedy algorithm, approximation, "
            "computer-assisted proof, exact rational certificates"
        )

    def _title_page(self, canvas, doc):
        self._set_metadata(canvas)
        canvas.saveState()
        canvas.setFillColor(MUTED)
        canvas.setFont("Helvetica", 7.5)
        canvas.drawCentredString(PAGE_W / 2, 10 * mm, self.metadata["status"])
        canvas.restoreState()

    def _normal_page(self, canvas, doc):
        self._set_metadata(canvas)
        canvas.saveState()
        canvas.setStrokeColor(RULE)
        canvas.setLineWidth(0.45)
        y = PAGE_H - 11.5 * mm
        canvas.line(LEFT, y, PAGE_W - RIGHT, y)
        canvas.setFillColor(MUTED)
        canvas.setFont("Helvetica", 7.4)
        canvas.drawString(LEFT, PAGE_H - 9.2 * mm, "GREEDY SUPERSTRINGS WITH AT MOST SIX INPUT WORDS")
        canvas.drawRightString(PAGE_W - RIGHT, 9.2 * mm, str(doc.page))
        canvas.setStrokeColor(RULE)
        canvas.line(LEFT, 12 * mm, PAGE_W - RIGHT, 12 * mm)
        canvas.restoreState()

    def beforeDocument(self):
        self._bookmark_counter = 0

    def afterFlowable(self, flowable):
        if not isinstance(flowable, Paragraph):
            return
        style_name = flowable.style.name
        if style_name not in {"H1", "H2"}:
            return
        level = 0 if style_name == "H1" else 1
        text = flowable.getPlainText()
        self._bookmark_counter += 1
        key = f"heading-{self._bookmark_counter}"
        self.canv.bookmarkPage(key)
        self.canv.addOutlineEntry(text, key, level=level, closed=False)
        self.notify("TOCEntry", (level, text, self.page, key))


class PaperRenderer:
    def __init__(self, source: Path, output: Path):
        self.source = source
        self.output = output
        self.metadata, self.lines = self._read_source()
        self.styles = self._styles()

    def _read_source(self):
        raw = self.source.read_text(encoding="utf-8").splitlines()
        if not raw or raw[0].strip() != "---":
            raise ValueError("missing metadata front matter")
        metadata = {}
        index = 1
        while index < len(raw) and raw[index].strip() != "---":
            key, value = raw[index].split(":", 1)
            metadata[key.strip()] = value.strip()
            index += 1
        required = {"title", "subtitle", "date", "status", "repository"}
        missing = required - metadata.keys()
        if missing:
            raise ValueError(f"missing metadata: {sorted(missing)}")
        return metadata, raw[index + 1 :]

    def _styles(self):
        base = getSampleStyleSheet()
        styles = {}
        styles["Body"] = ParagraphStyle(
            "Body",
            parent=base["BodyText"],
            fontName="Times-Roman",
            fontSize=9.35,
            leading=12.25,
            textColor=INK,
            alignment=TA_JUSTIFY,
            spaceAfter=5.8,
            allowWidows=0,
            allowOrphans=0,
        )
        styles["BodyLeft"] = ParagraphStyle(
            "BodyLeft", parent=styles["Body"], alignment=TA_LEFT
        )
        styles["Abstract"] = ParagraphStyle(
            "Abstract",
            parent=styles["Body"],
            fontSize=9.1,
            leading=12.1,
            leftIndent=7 * mm,
            rightIndent=7 * mm,
            spaceAfter=6,
        )
        styles["H1"] = ParagraphStyle(
            "H1",
            parent=base["Heading1"],
            fontName="Helvetica-Bold",
            fontSize=16.0,
            leading=19.0,
            textColor=NAVY,
            spaceBefore=12,
            spaceAfter=6.5,
            keepWithNext=True,
        )
        styles["H2"] = ParagraphStyle(
            "H2",
            parent=base["Heading2"],
            fontName="Helvetica-Bold",
            fontSize=11.5,
            leading=14.0,
            textColor=BLUE,
            spaceBefore=9,
            spaceAfter=4.5,
            keepWithNext=True,
        )
        styles["Title"] = ParagraphStyle(
            "Title",
            parent=base["Title"],
            fontName="Helvetica-Bold",
            fontSize=25,
            leading=29,
            textColor=NAVY,
            alignment=TA_LEFT,
            spaceAfter=8,
        )
        styles["Subtitle"] = ParagraphStyle(
            "Subtitle",
            parent=base["Normal"],
            fontName="Helvetica",
            fontSize=14,
            leading=18,
            textColor=TEAL,
            alignment=TA_LEFT,
            spaceAfter=5,
        )
        styles["Meta"] = ParagraphStyle(
            "Meta",
            parent=base["Normal"],
            fontName="Helvetica",
            fontSize=8.2,
            leading=10.5,
            textColor=MUTED,
            alignment=TA_LEFT,
        )
        styles["TOCTitle"] = ParagraphStyle(
            "TOCTitle",
            parent=styles["H1"],
            fontSize=18,
            leading=22,
            spaceBefore=0,
            spaceAfter=10,
        )
        styles["TheoremLabel"] = ParagraphStyle(
            "TheoremLabel",
            parent=base["Normal"],
            fontName="Helvetica-Bold",
            fontSize=8.2,
            leading=10.2,
            textColor=TEAL,
            spaceAfter=3.2,
        )
        styles["TheoremBody"] = ParagraphStyle(
            "TheoremBody",
            parent=styles["Body"],
            fontSize=9.15,
            leading=11.8,
            spaceAfter=3,
        )
        styles["Code"] = ParagraphStyle(
            "Code",
            parent=base["Code"],
            fontName="Courier",
            fontSize=7.25,
            leading=9.2,
            textColor=colors.HexColor("#263746"),
            leftIndent=0,
            rightIndent=0,
            spaceBefore=0,
            spaceAfter=0,
        )
        styles["TableHeader"] = ParagraphStyle(
            "TableHeader",
            parent=base["Normal"],
            fontName="Helvetica-Bold",
            fontSize=7.2,
            leading=8.8,
            textColor=WHITE,
            alignment=TA_LEFT,
        )
        styles["TableCell"] = ParagraphStyle(
            "TableCell",
            parent=base["Normal"],
            fontName="Times-Roman",
            fontSize=7.2,
            leading=8.8,
            textColor=INK,
            alignment=TA_LEFT,
        )
        styles["Reference"] = ParagraphStyle(
            "Reference",
            parent=styles["BodyLeft"],
            fontSize=8.1,
            leading=10.4,
            leftIndent=5 * mm,
            firstLineIndent=-5 * mm,
            spaceAfter=4.2,
        )
        styles["Bullet"] = ParagraphStyle(
            "Bullet",
            parent=styles["BodyLeft"],
            fontSize=9.0,
            leading=11.7,
            leftIndent=0,
            spaceAfter=2.5,
        )
        return styles

    @staticmethod
    def _soften_url(url: str) -> str:
        escaped = html.escape(url)
        return escaped.replace("/", "/&#8203;").replace("?", "?&#8203;").replace("&amp;", "&amp;&#8203;")

    def inline(self, text: str) -> str:
        tokens = []

        def stash(value):
            tokens.append(value)
            return f"@@TOKEN{len(tokens)-1}@@"

        text = re.sub(
            r"\[([^\]]+)\]\((https?://[^)]+)\)",
            lambda m: stash(
                f'<link href="{html.escape(m.group(2), quote=True)}" color="#285F8F">'
                f"{html.escape(m.group(1))}</link>"
            ),
            text,
        )
        text = re.sub(
            r"https?://\S+",
            lambda m: stash(
                f'<link href="{html.escape(m.group(0), quote=True)}" color="#285F8F">'
                f'<font size="7.4">{self._soften_url(m.group(0))}</font></link>'
            ),
            text,
        )
        text = re.sub(
            r"`([^`]+)`",
            lambda m: stash(
                f'<font name="Courier" size="8.0" color="#24445F">{html.escape(m.group(1))}</font>'
            ),
            text,
        )
        escaped = html.escape(text)
        escaped = re.sub(r"\*\*([^*]+)\*\*", r"<b>\1</b>", escaped)
        escaped = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<i>\1</i>", escaped)
        for index, token in enumerate(tokens):
            escaped = escaped.replace(f"@@TOKEN{index}@@", token)
        return escaped

    def paragraph(self, text, style="Body"):
        return Paragraph(self.inline(text), self.styles[style])

    def equation(self, lines, compact=False):
        wrapped = []
        for line in lines:
            if len(line) <= 103:
                wrapped.append(line)
            else:
                indent = len(line) - len(line.lstrip())
                wrapped.extend(
                    textwrap.wrap(
                        line,
                        width=103,
                        subsequent_indent=" " * min(indent + 4, 16),
                        break_long_words=False,
                        break_on_hyphens=False,
                    )
                )
        pre = Preformatted("\n".join(wrapped), self.styles["Code"])
        width = FRAME_W - (23 * mm if compact else 8 * mm)
        table = Table([[pre]], colWidths=[width], hAlign="LEFT")
        table.setStyle(
            TableStyle(
                [
                    ("BACKGROUND", (0, 0), (-1, -1), PALE_GRAY),
                    ("BOX", (0, 0), (-1, -1), 0.45, RULE),
                    ("LEFTPADDING", (0, 0), (-1, -1), 4 * mm),
                    ("RIGHTPADDING", (0, 0), (-1, -1), 4 * mm),
                    ("TOPPADDING", (0, 0), (-1, -1), 2.2 * mm),
                    ("BOTTOMPADDING", (0, 0), (-1, -1), 2.2 * mm),
                ]
            )
        )
        return [Spacer(1, 1.2), table, Spacer(1, 4.5)]

    def theorem_box(self, kind, title, content_lines):
        label = kind.upper() if not title else f"{kind.upper()} - {title}"
        inner = [Paragraph(self.inline(label), self.styles["TheoremLabel"])]
        inner.extend(self.parse_blocks(content_lines, in_box=True))
        box = Table([[inner]], colWidths=[FRAME_W - 7 * mm], hAlign="LEFT")
        shade = PALE_TEAL if kind.lower() in {"theorem", "corollary"} else PALE_BLUE
        box.setStyle(
            TableStyle(
                [
                    ("BACKGROUND", (0, 0), (-1, -1), shade),
                    ("LINEBEFORE", (0, 0), (0, -1), 2.2, TEAL if shade == PALE_TEAL else BLUE),
                    ("BOX", (0, 0), (-1, -1), 0.35, RULE),
                    ("LEFTPADDING", (0, 0), (-1, -1), 4 * mm),
                    ("RIGHTPADDING", (0, 0), (-1, -1), 4 * mm),
                    ("TOPPADDING", (0, 0), (-1, -1), 3 * mm),
                    ("BOTTOMPADDING", (0, 0), (-1, -1), 2.5 * mm),
                ]
            )
        )
        return [Spacer(1, 2), KeepTogether(box), Spacer(1, 5)]

    def markdown_table(self, rows):
        parsed = []
        for row_index, row in enumerate(rows):
            cells = [cell.strip() for cell in row.strip().strip("|").split("|")]
            if row_index == 1 and all(re.fullmatch(r":?-{3,}:?", c) for c in cells):
                continue
            rendered = []
            for cell in cells:
                if re.fullmatch(r"[0-9a-f]{64}", cell):
                    cell_markup = (
                        f'<font name="Courier" size="5.7">{cell[:32]}<br/>{cell[32:]}</font>'
                    )
                else:
                    cell_markup = self.inline(cell)
                style = "TableHeader" if not parsed else "TableCell"
                rendered.append(Paragraph(cell_markup, self.styles[style]))
            parsed.append(rendered)
        columns = len(parsed[0])
        if columns == 3:
            widths = [0.24 * FRAME_W, 0.23 * FRAME_W, 0.53 * FRAME_W]
        elif columns == 5:
            widths = [0.08 * FRAME_W, 0.12 * FRAME_W, 0.13 * FRAME_W, 0.13 * FRAME_W, 0.54 * FRAME_W]
        else:
            widths = [FRAME_W / columns] * columns
        table = Table(parsed, colWidths=widths, repeatRows=1, hAlign="LEFT")
        table.setStyle(
            TableStyle(
                [
                    ("BACKGROUND", (0, 0), (-1, 0), NAVY),
                    ("GRID", (0, 0), (-1, -1), 0.35, RULE),
                    ("VALIGN", (0, 0), (-1, -1), "TOP"),
                    ("LEFTPADDING", (0, 0), (-1, -1), 2.0 * mm),
                    ("RIGHTPADDING", (0, 0), (-1, -1), 2.0 * mm),
                    ("TOPPADDING", (0, 0), (-1, -1), 1.5 * mm),
                    ("BOTTOMPADDING", (0, 0), (-1, -1), 1.5 * mm),
                ]
            )
        )
        for index in range(1, len(parsed)):
            if index % 2 == 0:
                table.setStyle(TableStyle([("BACKGROUND", (0, index), (-1, index), PALE_GRAY)]))
        return [Spacer(1, 2), table, Spacer(1, 6)]

    def parse_blocks(self, lines, in_box=False):
        story = []
        i = 0
        paragraph_lines = []

        def flush_paragraph():
            if not paragraph_lines:
                return
            text = " ".join(line.strip() for line in paragraph_lines).strip()
            paragraph_lines.clear()
            if text:
                style = "TheoremBody" if in_box else ("Reference" if re.match(r"^\[[0-9]+\]", text) else "Body")
                story.append(self.paragraph(text, style))

        while i < len(lines):
            line = lines[i]
            stripped = line.strip()
            if not stripped:
                flush_paragraph()
                i += 1
                continue
            if stripped.startswith("::: "):
                flush_paragraph()
                descriptor = stripped[4:].strip()
                parts = descriptor.split(" ", 1)
                kind = parts[0]
                title = parts[1] if len(parts) == 2 else ""
                block = []
                i += 1
                while i < len(lines) and lines[i].strip() != "::: ".strip():
                    if lines[i].strip() == ":::":
                        break
                    block.append(lines[i])
                    i += 1
                story.extend(self.theorem_box(kind, title, block))
                i += 1
                continue
            if stripped.startswith("```"):
                flush_paragraph()
                code = []
                i += 1
                while i < len(lines) and not lines[i].strip().startswith("```"):
                    code.append(lines[i])
                    i += 1
                story.extend(self.equation(code, compact=in_box))
                i += 1
                continue
            if stripped.startswith("# "):
                flush_paragraph()
                story.append(CondPageBreak(32 * mm))
                story.append(Paragraph(self.inline(stripped[2:].strip()), self.styles["H1"]))
                i += 1
                continue
            if stripped.startswith("## "):
                flush_paragraph()
                story.append(CondPageBreak(20 * mm))
                story.append(Paragraph(self.inline(stripped[3:].strip()), self.styles["H2"]))
                i += 1
                continue
            if stripped.startswith("|"):
                flush_paragraph()
                table_rows = []
                while i < len(lines) and lines[i].strip().startswith("|"):
                    table_rows.append(lines[i])
                    i += 1
                story.extend(self.markdown_table(table_rows))
                continue
            if stripped.startswith("- "):
                flush_paragraph()
                bullets = []
                while i < len(lines) and lines[i].strip().startswith("- "):
                    bullets.append(
                        ListItem(
                            self.paragraph(lines[i].strip()[2:], "Bullet"),
                            leftIndent=4 * mm,
                        )
                    )
                    i += 1
                story.append(
                    ListFlowable(
                        bullets,
                        bulletType="bullet",
                        start="circle",
                        leftIndent=5 * mm,
                        bulletFontName="Helvetica",
                        bulletFontSize=5,
                        spaceAfter=5,
                    )
                )
                continue
            paragraph_lines.append(line)
            i += 1
        flush_paragraph()
        return story

    def split_abstract(self):
        start = None
        end = None
        for i, line in enumerate(self.lines):
            if line.strip() == "# Abstract":
                start = i
            elif start is not None and line.startswith("# "):
                end = i
                break
        if start is None or end is None:
            raise ValueError("abstract section not found")
        abstract_lines = self.lines[start + 1 : end]
        while abstract_lines and not abstract_lines[0].strip():
            abstract_lines.pop(0)
        return abstract_lines, self.lines[end:]

    def title_story(self, abstract_lines):
        repository = self.metadata["repository"]
        abstract_text = " ".join(x.strip() for x in abstract_lines if x.strip())
        badge = Table(
            [[Paragraph("EXACT COMPUTER-ASSISTED RESULT", self.styles["TheoremLabel"])]],
            colWidths=[57 * mm],
            hAlign="LEFT",
        )
        badge.setStyle(
            TableStyle(
                [
                    ("BACKGROUND", (0, 0), (-1, -1), PALE_TEAL),
                    ("BOX", (0, 0), (-1, -1), 0.6, TEAL),
                    ("LEFTPADDING", (0, 0), (-1, -1), 3 * mm),
                    ("RIGHTPADDING", (0, 0), (-1, -1), 3 * mm),
                    ("TOPPADDING", (0, 0), (-1, -1), 1.5 * mm),
                    ("BOTTOMPADDING", (0, 0), (-1, -1), 1.5 * mm),
                ]
            )
        )
        abstract_box = Table(
            [[Paragraph(self.inline(abstract_text), self.styles["Abstract"])]],
            colWidths=[FRAME_W - 4 * mm],
            hAlign="LEFT",
        )
        abstract_box.setStyle(
            TableStyle(
                [
                    ("BACKGROUND", (0, 0), (-1, -1), PALE_BLUE),
                    ("BOX", (0, 0), (-1, -1), 0.45, RULE),
                    ("LEFTPADDING", (0, 0), (-1, -1), 1.5 * mm),
                    ("RIGHTPADDING", (0, 0), (-1, -1), 1.5 * mm),
                    ("TOPPADDING", (0, 0), (-1, -1), 3.5 * mm),
                    ("BOTTOMPADDING", (0, 0), (-1, -1), 2.5 * mm),
                ]
            )
        )
        repo_markup = (
            f'<b>Artifact repository:</b> <link href="{html.escape(repository, quote=True)}" '
            f'color="#285F8F">{html.escape(repository)}</link>'
        )
        return [
            Spacer(1, 10 * mm),
            badge,
            Spacer(1, 12 * mm),
            Paragraph(self.inline(self.metadata["title"]), self.styles["Title"]),
            Paragraph(self.inline(self.metadata["subtitle"]), self.styles["Subtitle"]),
            Spacer(1, 4 * mm),
            HRFlowable(width="100%", thickness=1.1, color=TEAL, spaceAfter=6 * mm),
            Paragraph(f'<b>{html.escape(self.metadata["date"])}</b>', self.styles["Meta"]),
            Paragraph(html.escape(self.metadata["status"]), self.styles["Meta"]),
            Spacer(1, 9 * mm),
            Paragraph("ABSTRACT", self.styles["TheoremLabel"]),
            abstract_box,
            Spacer(1, 8 * mm),
            Paragraph(repo_markup, self.styles["Meta"]),
            Spacer(1, 4 * mm),
            Paragraph(
                "Scope: arbitrary alphabet and word lengths; one through six reduced input words; every greedy tie resolution.",
                self.styles["Meta"],
            ),
            NextPageTemplate("normal"),
            PageBreak(),
        ]

    def toc_story(self):
        toc = TableOfContents()
        toc.levelStyles = [
            ParagraphStyle(
                "TOC1",
                fontName="Helvetica",
                fontSize=9.2,
                leading=12,
                leftIndent=0,
                firstLineIndent=0,
                textColor=INK,
                spaceBefore=2,
            ),
            ParagraphStyle(
                "TOC2",
                fontName="Helvetica",
                fontSize=8.5,
                leading=10.5,
                leftIndent=7 * mm,
                firstLineIndent=0,
                textColor=MUTED,
                spaceBefore=1,
            ),
        ]
        return [
            Paragraph("Contents", self.styles["TOCTitle"]),
            HRFlowable(width="100%", thickness=0.6, color=RULE, spaceAfter=4 * mm),
            toc,
            PageBreak(),
        ]

    def build(self):
        self.output.parent.mkdir(parents=True, exist_ok=True)
        abstract, body = self.split_abstract()
        story = self.title_story(abstract) + self.toc_story() + self.parse_blocks(body)
        doc = FormalDocTemplate(
            str(self.output),
            self.metadata,
            leftMargin=LEFT,
            rightMargin=RIGHT,
            topMargin=TOP,
            bottomMargin=BOTTOM,
            pageCompression=1,
        )
        doc.multiBuild(story)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    PaperRenderer(args.source, args.output).build()
    print(args.output.resolve())


if __name__ == "__main__":
    main()
