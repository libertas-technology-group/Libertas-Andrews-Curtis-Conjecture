"""Sphinx configuration for the Andrews–Curtis documentation.

This is the platform-standard Sphinx ``conf.py``, copied from the canonical
AGENTS_REPO_STANDARDS template (Libertas-AI-Core) as used by Libertas-Fluid-Solver.
The product placeholders differ; the structure does not. The corpus ships no
Python package, so the mock list is empty.

For the full list of built-in configuration values, see the documentation:
https://www.sphinx-doc.org/en/master/usage/configuration.html
"""

# Configuration file for the Sphinx documentation builder.

import sys
from pathlib import Path
from unittest.mock import MagicMock

# -- Path setup --------------------------------------------------------------
_docs_dir = Path(__file__).resolve().parent
_repo_root = _docs_dir.parent

# Add the engine root to sys.path so autodoc can find the package.
sys.path.insert(0, str(_repo_root))

# -- Pre-mock third-party packages for CI builds ------------------------------
# In CI only sphinx/furo are installed. List every third-party package the
# engine imports so autodoc can extract docstrings anyway. MagicMock handles
# attribute access and submodule imports autodoc_mock_imports cannot.
import importlib.machinery  # noqa: E402


def _install_mock(name: str) -> None:
    """Register a spec-aware MagicMock for ``name`` in ``sys.modules``.

    A plain MagicMock has no ``__spec__``, which breaks engine code that
    probes availability with ``importlib.util.find_spec`` (see
    ``libertas_fluid_solver/fourier_transforms/backend_probing.py``: it calls
    ``find_spec("cupy")`` at import time). Giving the mock a real ModuleSpec
    makes ``find_spec`` return the spec (never ``None``) instead of raising
    ``ValueError: <name>.__spec__ is not set``.
    """
    module = MagicMock()
    module.__spec__ = importlib.machinery.ModuleSpec(name, None)
    sys.modules[name] = module


_MOCK_PACKAGES = []
for _pkg in _MOCK_PACKAGES:
    try:
        __import__(_pkg)
    except ImportError:
        _install_mock(_pkg)

# -- Project information -----------------------------------------------------
project = "Libertas Andrews–Curtis"
copyright = "2026, Libertas Technology Group Limited"
author = "Libertas Technology Group Limited · Libertas Superintelligence ©"

# -- General configuration ---------------------------------------------------
extensions = [
    "sphinx.ext.autodoc",
    "sphinx.ext.napoleon",
    "sphinx.ext.viewcode",
    "sphinx.ext.intersphinx",
    "sphinx.ext.graphviz",
    "sphinx.ext.mathjax",
]

# Graphviz settings
graphviz_output_format = "svg"

templates_path = ["_templates"]
exclude_patterns = [
    "_build",
    "_includes",
    "Thumbs.db",
    ".DS_Store",
    "__pycache__",
    ".venv",
    "node_modules",
]

# -- Napoleon settings (NumPy-style docstrings) ------------------------------
napoleon_numpy_docstring = True
napoleon_google_docstring = False
napoleon_include_init_with_doc = True
napoleon_include_private_with_doc = False
napoleon_include_special_with_doc = True
napoleon_use_admonition_for_examples = True
napoleon_use_admonition_for_notes = True
napoleon_use_admonition_for_references = True
napoleon_use_ivar = False
napoleon_use_param = True
napoleon_use_rtype = True

# -- Autodoc settings --------------------------------------------------------
autodoc_member_order = "bysource"
autodoc_default_options = {
    "members": True,
    "undoc-members": True,
    "show-inheritance": True,
}

# Only use class docstring, not __init__ (prevents Pydantic field duplication)
autodoc_class_content = "class"

# Platform-wide unified suppression list (matches every repository):
#   ref.citation / ref.footnote — guides use citation/footnote markup whose
#     references may span files; kept for uniformity across the platform.
#   ref.python — intentional third-party references left unlinked.
#   duplicate.object / autodoc.duplicate_object — Pydantic v2 duplicate field
#     warnings (also handled by the logging filter in setup() below).
#   docutils — the engine's NumPy docstrings carry inline ``**kwargs``
#     signature tokens (e.g. ``format_cost_table(**kwargs)``) that docutils
#     parses as unclosed strong markup. The source is out of scope for the
#     docs tree, so the parse warning is suppressed here.
suppress_warnings = [
    "ref.citation",
    "ref.footnote",
    "ref.python",
    "autodoc.duplicate_object",
    "duplicate.object",
    "docutils",
]

# -- Intersphinx settings ----------------------------------------------------
intersphinx_mapping = {
    "python": ("https://docs.python.org/3", None),
}

# -- Mock imports (packages not installed in the docs build environment) -----
# Every third-party dependency the engine imports must be listed here so that
# autodoc can import all application modules and extract docstrings in CI
# where only sphinx and furo are installed.
autodoc_mock_imports = []

# -- Options for HTML output -------------------------------------------------
html_theme = "furo"

html_meta = {
    "description": "Libertas Superintelligence provides Superintelligence and AI software to institutions where privacy and data security are non-negotiable. This corpus is one stress test of the platform: a machine-checked Lean 4 corpus on the Andrews-Curtis conjecture, with universal laws and named open inputs.",
    "keywords": "Libertas Superintelligence, Cognitive World Models, white-box superintelligence, Andrews-Curtis conjecture, Lean 4, formal verification, combinatorial group theory, machine-checked mathematics, applied and industrial AI",
}
html_title = "Libertas Andrews–Curtis — Documentation"
html_static_path = ["_static"]
html_extra_path = ["dashboard.html"]
html_css_files = ["custom.css"]
html_show_sphinx = False

html_theme_options = {
    "sidebar_hide_name": True,
    "navigation_with_keys": True,
    "top_of_page_buttons": [],
    "light_css_variables": {
        "color-brand-primary": "#1f1f1f",
        "color-brand-content": "#1f1f1f",
        "color-background-primary": "#fbfbf9",
        "color-background-secondary": "#f7f7f5",
        "color-background-hover": "#f0f0ee",
        "color-background-hover--transparent": "#f0f0ee00",
        "color-background-border": "#eaeae6",
        "color-background-item": "#ffffff",
        "color-foreground-primary": "#1f1f1f",
        "color-foreground-secondary": "#555555",
        "color-foreground-muted": "#737373",
        "color-foreground-border": "#eaeae6",
        "color-sidebar-background": "#f7f7f5",
        "color-sidebar-background-border": "#eaeae6",
        "color-sidebar-brand-text": "#1f1f1f",
        "color-sidebar-caption-text": "#737373",
        "color-sidebar-link-text": "#1f1f1f",
        "color-sidebar-link-text--top-level": "#1f1f1f",
        "color-sidebar-item-background--current": "#efeeed",
        "color-sidebar-item-background--hover": "#f0f0ee",
        "color-sidebar-item-expander-background": "transparent",
        "color-sidebar-item-expander-background--hover": "#eaeae6",
        "color-sidebar-search-background": "#ffffff",
        "color-sidebar-search-background--focus": "#ffffff",
        "color-sidebar-search-border": "#eaeae6",
        "color-sidebar-search-icon": "#737373",
        "color-header-background": "#fbfbf9",
        "color-header-border": "#eaeae6",
        "color-header-text": "#1f1f1f",
        "color-toc-background": "#fbfbf9",
        "color-toc-title-text": "#1f1f1f",
        "color-toc-item-text": "#555555",
        "color-toc-item-text--hover": "#1f1f1f",
        "color-toc-item-text--active": "#1f1f1f",
        "color-card-background": "#ffffff",
        "color-card-border": "#eaeae6",
        "color-card-marginals-background": "#f7f7f5",
        "color-table-header-background": "#f7f7f5",
        "color-table-border": "#eaeae6",
        "color-inline-code-background": "#f7f7f5",
        "color-highlighted-background": "#efeeed",
        "color-link": "#1f1f1f",
        "color-link-underline": "#c0c0bc",
        "color-link--hover": "#000000",
        "color-link-underline--hover": "#1f1f1f",
        "color-api-background": "#f7f7f5",
        "color-api-background-hover": "#f0f0ee",
        "color-api-overall": "#1f1f1f",
        "color-api-name": "#1f1f1f",
        "color-api-pre-name": "#555555",
        "color-api-paren": "#737373",
        "color-api-keyword": "#1f1f1f",
        "font-stack": "'GT Standard', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif",
        "font-stack--monospace": (
            "'GT America Mono', ui-monospace, 'SFMono-Regular', Consolas, monospace"
        ),
        "font-stack--headings": (
            "'GT Standard', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif"
        ),
        "font-size--normal": "14px",
        "font-size--small": "12px",
        "font-size--small--2": "11px",
        "sidebar-width": "280px",
        "sidebar-width--mobile": "320px",
        "content-padding": "4em",
        "content-padding--small": "2em",
    },
    # Classic Dark theme (matches frontend .theme-classic-dark)
    "dark_css_variables": {
        "color-brand-primary": "#ececec",
        "color-brand-content": "#ececec",
        "color-background-primary": "#212121",
        "color-background-secondary": "#2f2f2f",
        "color-background-hover": "#383838",
        "color-background-hover--transparent": "#38383800",
        "color-background-border": "#383838",
        "color-background-item": "#2d2d2d",
        "color-foreground-primary": "#ececec",
        "color-foreground-secondary": "#b0b0b0",
        "color-foreground-muted": "#999999",
        "color-foreground-border": "#383838",
        "color-sidebar-background": "#2f2f2f",
        "color-sidebar-background-border": "#383838",
        "color-sidebar-brand-text": "#ececec",
        "color-sidebar-caption-text": "#999999",
        "color-sidebar-link-text": "#ececec",
        "color-sidebar-link-text--top-level": "#ececec",
        "color-sidebar-item-background--current": "#383838",
        "color-sidebar-item-background--hover": "#383838",
        "color-sidebar-item-expander-background": "transparent",
        "color-sidebar-item-expander-background--hover": "#383838",
        "color-sidebar-search-background": "#212121",
        "color-sidebar-search-background--focus": "#212121",
        "color-sidebar-search-border": "#383838",
        "color-sidebar-search-icon": "#999999",
        "color-header-background": "#212121",
        "color-header-border": "#383838",
        "color-header-text": "#ececec",
        "color-toc-background": "#212121",
        "color-toc-title-text": "#ececec",
        "color-toc-item-text": "#b0b0b0",
        "color-toc-item-text--hover": "#ececec",
        "color-toc-item-text--active": "#ececec",
        "color-card-background": "#2d2d2d",
        "color-card-border": "#383838",
        "color-card-marginals-background": "#2f2f2f",
        "color-table-header-background": "#2f2f2f",
        "color-table-border": "#383838",
        "color-inline-code-background": "#2d2d2d",
        "color-highlighted-background": "#383838",
        "color-link": "#ececec",
        "color-link-underline": "#555555",
        "color-link--hover": "#ffffff",
        "color-link-underline--hover": "#ececec",
        "color-api-background": "#2d2d2d",
        "color-api-background-hover": "#383838",
        "color-api-overall": "#ececec",
        "color-api-name": "#ececec",
        "color-api-pre-name": "#b0b0b0",
        "color-api-paren": "#999999",
        "color-api-keyword": "#ececec",
        "font-stack": "'GT Standard', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif",
        "font-stack--monospace": (
            "'GT America Mono', ui-monospace, 'SFMono-Regular', Consolas, monospace"
        ),
        "font-stack--headings": (
            "'GT Standard', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif"
        ),
        "font-size--normal": "14px",
        "font-size--small": "12px",
        "font-size--small--2": "11px",
        "sidebar-width": "280px",
        "color-brand-visited": "#ececec",
        "color-link--visited": "#ececec",
        "color-link-underline--visited": "#555555",
        "color-link--visited--hover": "#ffffff",
        "color-link-underline--visited--hover": "#ececec",
    },
}

# ---------------------------------------------------------------------------
# Linkcheck configuration
# ---------------------------------------------------------------------------
linkcheck_timeout = 10
linkcheck_retries = 2
linkcheck_workers = 4
# Ignore known transient or auth-conditioned URLs
linkcheck_ignore = [
    r"http://localhost.*",  # Local-only URLs
    # DOI resolver returns 403 to non-browser clients (bot protection);
    # the DOIs themselves are valid. Same exception as the Flow docs.
    r"https://doi\.org/.*",
    # Broken/truncated URL inside the engine's docstrings (transform_api.py
    # §source, out of the docs tree's scope): the encoded form 404s.
    r"https://www\.fftw\.org/doc/One_002dDimensional-DFTs-of-Real.*",
]


# -- Suppress duplicate object description warnings --------------------------
# autodoc documents the ProviderAdapter ``provider_name`` attribute both from
# the ABC and from its inherited members, producing "duplicate object
# description" messages with no warning type code (cannot be suppressed via
# suppress_warnings). Install a log filter that drops exactly these messages,
# leaving all other warnings intact (canonical AGENTS_REPO_STANDARDS template).
import logging  # noqa: E402


class _DuplicateObjectFilter(logging.Filter):
    """Drops duplicate object-description warnings from Sphinx output.

    Matches only "duplicate object description" messages that carry no Sphinx
    warning ``type`` attribute (the Python-domain logger emits them without
    one, so ``suppress_warnings`` cannot match them).
    """

    def filter(self, record: logging.LogRecord) -> bool:
        msg = record.getMessage()
        return not (
            "duplicate object description" in msg and "use :no-index: for one of them" in msg
        )


def setup(app):  # noqa: ANN001, ANN201, ARG001  (Sphinx passes the app by signature)
    """Install duplicate-object filters during Sphinx setup."""
    logging.getLogger("sphinx").addFilter(_DuplicateObjectFilter())
    logging.getLogger("sphinx.domains.python").addFilter(_DuplicateObjectFilter())
