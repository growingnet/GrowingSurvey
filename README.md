# The Neuron Addition Problem: A Survey on Growing Neural Networks

[![survey](https://github.com/growingnet/GrowingSurvey/actions/workflows/survey.yml/badge.svg)](https://github.com/growingnet/GrowingSurvey/actions/workflows/survey.yml)

This repository contains the LaTeX sources of the survey
[The Neuron Addition Problem: A Survey on Growing Neural Networks](https://hal.science/hal-05842579).

- [Version on HAL](https://hal.science/hal-05842579)
- [Latest PDF](https://github.com/growingnet/GrowingSurvey/releases/download/survey-latest/neuron_addition_survey.pdf),
  rebuilt automatically whenever the sources change on `main`

The survey is complemented and continued by the
[Growing Wiki](https://growingnet.github.io/growing_wiki)
([sources](https://github.com/growingnet/growing_wiki)).

## Citation

If you use the survey in your work, please cite it. It has not been published yet; the
entry below will be replaced by the published reference.

<!-- TODO(citation): replace with the published reference of the survey. -->

```bibtex
@unpublished{daveyNeuronAdditionProblem2026,
  TITLE = {{The Neuron Addition Problem: A Survey on Growing Neural Networks}},
  AUTHOR = {Davey, Alex and Rudkiewicz, Théo and Rivaud, Stéphane and Douka, Stella and Houdouin, Félix and Mille, Julien and Shilova, Alena and Charpiat, Guillaume and Chevallier, Sylvain},
  URL = {https://hal.science/hal-05842579},
  YEAR = {2026},
  MONTH = Oct,
  PDF = {https://hal.science/hal-05842579v1/file/main.pdf},
  HAL_ID = {hal-05842579},
}
```

## Repository Layout

- `main.tex`: preamble, title page and structure of the survey
- `math_commands.tex`: mathematical macros
- `subtex/`: one file per section
- `figures/`: TikZ figures
- `bibliography.bib`: bibliography

## Build Locally

With a TeX Live installation, run:

```bash
latexmk -pdf main.tex
```

The PDF is written to `main.pdf`.

## Contributing

Changes go through pull requests. The CI compiles the survey and fails on LaTeX errors
and on undefined references or citations.

The repository uses [pre-commit](https://pre-commit.com/) hooks: whitespace fixes,
spell checking with [codespell](https://github.com/codespell-project/codespell), and no
direct commits to `main`. With [uv](https://docs.astral.sh/uv/) installed, enable them
with:

```bash
uv tool install pre-commit
pre-commit install
```

To run them on all files, use `pre-commit run --all-files`.

## License

The survey is licensed under
[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/). See
[LICENSE](LICENSE).
