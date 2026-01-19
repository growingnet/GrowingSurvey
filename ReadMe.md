# GrowingSurvey

[![Compile Typst to PDF](https://github.com/growingnet/GrowingSurvey/actions/workflows/compile-typst.yml/badge.svg)](https://github.com/growingnet/GrowingSurvey/actions/workflows/compile-typst.yml)

## Download the PDF

The latest compiled version of the document is automatically generated and available here:

**[Download Latest PDF](https://github.com/growingnet/GrowingSurvey/releases/latest/download/main.pdf)**

You can also find all releases on the [Releases page](https://github.com/growingnet/GrowingSurvey/releases).

## Building Locally
This project uses [Typst](https://typst.app/) for document preparation. To compile locally:

1. Install Typst: https://github.com/typst/typst#installation
2. Run:
   ```bash
   typst compile main.typ
   ```

## Project Structure

- `main.typ` - Main document
- `subtyp/` - Sub-documents and sections
- `typst/` - Custom commands and styling
- `references.bib` - Bibliography
