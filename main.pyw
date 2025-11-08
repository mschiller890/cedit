import json
import os
import sys
import shutil
import subprocess
import fitz
import re
import gc
import weakref
import traceback
from typing import Dict
import threading
import psutil
import queue
from datetime import datetime

from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QTreeView, QFileSystemModel, QTabWidget,
    QWidget, QVBoxLayout, QHBoxLayout, QPlainTextEdit, QTextEdit, QSplitter, QAction, QFileDialog, QLabel,
    QDialog, QFormLayout, QComboBox, QSpinBox, QPushButton, QCheckBox, QScrollArea, QLineEdit, QMessageBox,
    QInputDialog, QGridLayout, QFrame, QSlider, QProgressBar,
)

from PyQt5.QtGui import QFont, QColor, QSyntaxHighlighter, QTextCharFormat, QPainter, QImage, QPixmap, QIcon
from PyQt5.QtCore import Qt, QDir, QTimer, QRect, pyqtSignal, QObject, QSize
from PyQt5 import QtGui

if getattr(sys, 'frozen', False): 
    base_path = os.path.dirname(sys.executable)
else:
    base_path = os.path.dirname(__file__)
    
config_dir = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "cedit")
os.makedirs(config_dir, exist_ok=True)
settings_path = os.path.join(config_dir, "settings.json")

class StatusManager:
    """Manages status bar messages with timestamps"""
    last_update_time = None
    status_bar = None
    current_message = ""
    timer = None

    @classmethod
    def init(cls, status_bar):
        cls.status_bar = status_bar

        # Create a timer that updates every second
        cls.timer = QTimer()
        cls.timer.timeout.connect(cls.refresh_message)
        cls.timer.start(1000)  # every 1000 ms = 1 second

    @classmethod
    def show_message(cls, message, file_path=None):
        """
        message: main message to show (e.g., "Opened")
        file_path: optional full file path; only filename will be displayed
        """
        if file_path:
            filename = os.path.basename(file_path)
            cls.current_message = f"{message} {filename}"
        else:
            cls.current_message = message

        cls.last_update_time = datetime.now()
        cls.refresh_message()  # immediately show it

    @classmethod
    def refresh_message(cls):
        if cls.status_bar is None or not cls.current_message:
            return

        now = datetime.now()
        elapsed = ""
        if cls.last_update_time:
            delta = now - cls.last_update_time
            minutes, seconds = divmod(delta.total_seconds(), 60)
            elapsed = f" ({int(minutes)}m {int(seconds)}s ago)"
        cls.status_bar.showMessage(cls.current_message + elapsed)


class MemoryManager:
    """Centralized memory management to prevent leaks"""
    def __init__(self):
        self._cache_cleanup_timer = QTimer()
        self._cache_cleanup_timer.timeout.connect(self._cleanup_caches)
        self._cache_cleanup_timer.start(30000)  # Clean every 30 seconds
        self._memory_monitor_timer = QTimer()
        self._memory_monitor_timer.timeout.connect(self._monitor_memory)
        self._memory_monitor_timer.start(10000)  # Monitor every 10 seconds
        self._max_memory_mb = 500  # Max memory usage in MB
        self._caches = []
    
    def register_cache(self, cache_dict, max_size=100):
        """Register a cache for automatic cleanup"""
        self._caches.append((cache_dict, max_size))
    
    def _cleanup_caches(self):
        """Clean up all registered caches"""
        for cache_dict, max_size in self._caches:
            if len(cache_dict) > max_size:
                # Remove oldest entries (simple FIFO)
                items_to_remove = len(cache_dict) - max_size
                keys_to_remove = list(cache_dict.keys())[:items_to_remove]
                for key in keys_to_remove:
                    del cache_dict[key]
        gc.collect()
    
    def _monitor_memory(self):
        """Monitor memory usage and force cleanup if needed"""
        try:
            process = psutil.Process()
            memory_mb = process.memory_info().rss / 1024 / 1024
            if memory_mb > self._max_memory_mb:
                self._cleanup_caches()
                for _ in range(3):
                    gc.collect()
        except Exception:
            pass

class FileWorker(QObject):
    """Worker thread for file operations"""
    file_loaded = pyqtSignal(str, str)  # file_path, content
    file_error = pyqtSignal(str, str)   # file_path, error
    
    def __init__(self):
        super().__init__()
        self._work_queue = queue.Queue()
        self._stop_event = threading.Event()
        self._thread = threading.Thread(target=self._worker_loop, daemon=True)
        self._thread.start()
    
    def load_file(self, file_path):
        """Queue a file for loading"""
        self._work_queue.put(('load', file_path))
    
    def _worker_loop(self):
        """Main worker loop"""
        while not self._stop_event.is_set():
            file_path = None
            try:
                operation, file_path = self._work_queue.get(timeout=1.0)
                if operation == 'load':
                    self._load_file_sync(file_path)
            except queue.Empty:
                continue
            except Exception as e:
                if file_path:
                    self.file_error.emit(file_path, str(e))
    
    def _load_file_sync(self, file_path):
        """Load file synchronously in worker thread"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            self.file_loaded.emit(file_path, content)
        except Exception as e:
            self.file_error.emit(file_path, str(e))
    
    def stop(self):
        """Stop the worker thread"""
        self._stop_event.set()
        if self._thread.is_alive():
            self._thread.join(timeout=1.0)

# Global instances
memory_manager = MemoryManager()
file_worker = FileWorker()

class MarkdownHtmlHighlighter(QSyntaxHighlighter):
    def __init__(self, document):
        super().__init__(document)
        self.highlightingRules = []
        self._compiled_rules = []  # Cache compiled regex patterns
        self._last_highlighted_text = ""
        self._highlight_cache = {}  # Cache highlighting results
        
        # Register cache with memory manager
        memory_manager.register_cache(self._highlight_cache, max_size=50)

        # --- Markdown comment lines (!!...) ---
        self._add_rule(r'^!!.*', QColor("#6e7681"), italic=True)                # Comment lines

        # --- Markdown formats ---
        self._add_rule(r'^(#+\s.*)', QColor("#42A5F5"), bold=True)           # Headings
        self._add_rule(r'(\*\*.*?\*\*|__.*?__)', QColor("#F06292"), bold=True)  # Bold
        self._add_rule(r'(\*.*?\*|_.*?_)', QColor("#BA68C8"), italic=True)      # Italic
        self._add_rule(r'`[^`]+`', QColor("#FFB74D"), font_family="monospace")  # Inline code
        self._add_rule(r'\[.*?\]\(.*?\)', QColor("#4DB6AC"), underline=True)    # Links
        self._add_rule(r'^\s*>\s.*', QColor("#8D6E63"))                         # Blockquotes

        # --- HTML formats ---
        self._add_rule(r'</?\w+.*?>', QColor("#29B6F6"), bold=True)            # Tags
        self._add_rule(r'(\w+)=', QColor("#FF7043"))                            # Attributes
        self._add_rule(r'".*?"', QColor("#81C784"))                             # Attribute values double quotes
        self._add_rule(r"'.*?'", QColor("#81C784"))                             # Attribute values single quotes
        self._add_rule(r'<!--.*?-->', QColor("#9E9E9E"), italic=True)           # Comments

    def _add_rule(self, pattern, color, bold=False, italic=False, underline=False, font_family=None):
        """Helper to compile regex once and store formatting."""
        fmt = QTextCharFormat()
        fmt.setForeground(color)
        if bold:
            fmt.setFontWeight(QFont.Bold)
        if italic:
            fmt.setFontItalic(True)
        if underline:
            fmt.setFontUnderline(True)
        if font_family:
            fmt.setFontFamily(font_family)
        compiled_pattern = re.compile(pattern)
        self.highlightingRules.append((compiled_pattern, fmt))
        self._compiled_rules.append((compiled_pattern, fmt))

    def highlightBlock(self, text):
        # Check cache first
        if text in self._highlight_cache:
            for start, end, fmt in self._highlight_cache[text]:
                self.setFormat(start, end - start, fmt)
            return
        
        # Cache results for future use
        highlights = []
        for pattern, fmt in self._compiled_rules:
            for match in pattern.finditer(text):
                start, end = match.span()
                self.setFormat(start, end - start, fmt)
                highlights.append((start, end, fmt))
        
        # Cache the results (limit cache size)
        if len(self._highlight_cache) > 100:
            # Remove oldest entries
            oldest_key = next(iter(self._highlight_cache))
            del self._highlight_cache[oldest_key]
        self._highlight_cache[text] = highlights

class LineNumberArea(QWidget):
    def __init__(self, editor):
        super().__init__(editor)
        # Use weak reference to avoid circular references
        self.codeEditor = weakref.proxy(editor)
        self._cached_width = 0
        self._cached_digits = 0

    def sizeHint(self):
        width = self.codeEditor.lineNumberAreaWidth()
        if width != self._cached_width:
            self._cached_width = width
        return QSize(width, 0)

    def paintEvent(self, a0):
        self.codeEditor.lineNumberAreaPaintEvent(a0)

class CodeEditor(QPlainTextEdit):
    """Enhanced plain text editor with line numbers and syntax highlighting"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFont(QFont("JetBrains Mono", 12))
        self.highlighter = MarkdownHtmlHighlighter(self.document())
        
        # Performance optimizations
        self._last_zoom_level = 12
        self._zoom_timer = QTimer()
        self._zoom_timer.setSingleShot(True)
        self._zoom_timer.timeout.connect(self._apply_zoom)
        
        # Debounce text changes for better performance
        self._text_change_timer = QTimer()
        self._text_change_timer.setSingleShot(True)
        self._text_change_timer.timeout.connect(self._on_text_changed_debounced)
        self._pending_text_changes = False

        self.lineNumberArea = LineNumberArea(self)
        self.blockCountChanged.connect(self.updateLineNumberAreaWidth)
        self.updateRequest.connect(self.updateLineNumberArea)
        self.cursorPositionChanged.connect(self.lineNumberArea.update)
        self.updateLineNumberAreaWidth(0)

    # ----------------- Event Handlers -----------------
    def keyPressEvent(self, e):
        if e and e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            if e.key() in (Qt.Key.Key_Plus, Qt.Key.Key_Equal):
                self._zoom(1)
                return
            elif e.key() == Qt.Key.Key_Minus:
                self._zoom(-1)
                return
            elif e.key() == Qt.Key.Key_0:
                parent_font = getattr(self.parent(), "parent", lambda: None)()
                if parent_font:
                    self.setFont(QFont(parent_font.font_family, parent_font.font_size))
                return
        super().keyPressEvent(e)

    def wheelEvent(self, e):
        if e and e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            self._zoom(1 if e.angleDelta().y() > 0 else -1)
        else:
            super().wheelEvent(e)

    def resizeEvent(self, e):
        super().resizeEvent(e)
        cr = self.contentsRect()
        self.lineNumberArea.setGeometry(
            cr.left(), cr.top(), self.lineNumberAreaWidth(), cr.height()
        )

    # ----------------- Helper Methods -----------------
    def _zoom(self, direction: int):
        new_size = max(6, self.font().pointSize() + direction)
        if new_size != self._last_zoom_level:
            self._last_zoom_level = new_size
            self._zoom_timer.start(50)  # Debounce zoom changes
    
    def _apply_zoom(self):
        font = self.font()
        font.setPointSize(self._last_zoom_level)
        self.setFont(font)
    
    def _on_text_changed_debounced(self):
        if self._pending_text_changes:
            self._pending_text_changes = False
            # Emit text changed signal for parent handling
            parent = self.parent()
            if parent and hasattr(parent, '_on_text_changed'):
                parent._on_text_changed()
            elif parent and hasattr(parent, '_trigger_preview_update'):
                parent._trigger_preview_update()

    def lineNumberAreaWidth(self):
        block_count = self.blockCount()
        digits = len(str(max(1, block_count)))
        return 3 + self.fontMetrics().width('9') * digits

    def updateLineNumberAreaWidth(self, _):
        self.setViewportMargins(self.lineNumberAreaWidth(), 0, 0, 0)

    def updateLineNumberArea(self, rect, dy):
        if dy:
            self.lineNumberArea.scroll(0, dy)
        else:
            self.lineNumberArea.update(0, rect.y(), self.lineNumberArea.width(), rect.height())
        viewport = self.viewport()
        if viewport and rect.contains(viewport.rect()):
            self.updateLineNumberAreaWidth(0)

    def lineNumberAreaPaintEvent(self, event):
        painter = QPainter(self.lineNumberArea)
        painter.fillRect(event.rect(), QColor("#232629"))

        block = self.firstVisibleBlock()
        block_number = block.blockNumber()
        top = self.blockBoundingGeometry(block).translated(self.contentOffset()).top()
        bottom = top + self.blockBoundingRect(block).height()
        line_height = self.fontMetrics().height()
        width = self.lineNumberArea.width() - 2

        while block.isValid() and top <= event.rect().bottom():
            if block.isVisible() and bottom >= event.rect().top():
                painter.setPen(QColor("#666"))
                painter.drawText(0, int(top), width, line_height, Qt.AlignmentFlag.AlignRight, str(block_number + 1))
            block = block.next()
            block_number += 1
            top = bottom
            bottom = top + self.blockBoundingRect(block).height()

class EditorTab(QWidget):
    """Tab widget containing a code editor"""
    
    def __init__(self, file_path=None):
        super().__init__()
        self.file_path = file_path
        self._saved_text = ""
        self._is_loading = True
        self._text_change_timer = QTimer()
        self._text_change_timer.setSingleShot(True)
        self._text_change_timer.timeout.connect(self._on_text_changed_debounced)

        layout = QVBoxLayout(self)
        self.editor = CodeEditor()
        layout.addWidget(self.editor)

        # Connect file worker signals
        file_worker.file_loaded.connect(self._on_file_loaded)
        file_worker.file_error.connect(self._on_file_error)

        # Load file if provided
        if file_path:
            self._is_loading = True
            file_worker.load_file(file_path)
        else:
            self._is_loading = False

        # Connect after setting initial text to avoid triggering
        self.editor.textChanged.connect(self._on_text_changed)
        self.editor.cursorPositionChanged.connect(self._update_cursor_position)

        # Cache reference to main window if available
        self._main_window = None
    
    def _update_cursor_position(self):
        """Update status bar with cursor position"""
        if self._main_window is None:
            parent = self.parent()
            self._main_window = parent.parent() if parent and parent.parent() else None
        
        if self._main_window:
            cursor = self.editor.textCursor()
            line = cursor.blockNumber() + 1
            col = cursor.columnNumber() + 1
            StatusManager.show_message(f"Line {line}, Column {col}")
    
    def _on_file_loaded(self, file_path, content):
        """Handle file loaded signal from worker thread"""
        if file_path == self.file_path:
            self._saved_text = content
            self.editor.setPlainText(content)
            self._is_loading = False
    
    def _on_file_error(self, file_path, error):
        """Handle file error signal from worker thread"""
        if file_path == self.file_path:
            self.editor.setPlainText(f"Error opening file: {error}")
            self._is_loading = False
    

    def is_modified(self):
        return self.editor.toPlainText() != (self._saved_text or "")

    def mark_saved(self):
        self._saved_text = self.editor.toPlainText()

    def _on_text_changed(self):
        if self._is_loading:
            return
        
        # Debounce text changes to improve performance
        self._text_change_timer.start(300)  # 300ms debounce
    
    def _on_text_changed_debounced(self):
        if self._main_window is None:
            parent = self.parent()
            self._main_window = parent.parent() if parent and parent.parent() else None

        if self._main_window and hasattr(self._main_window, "update_tab_title_modified"):
            self._main_window.update_tab_title_modified(self)

    def close_tab(self):
        # Stop timers
        if hasattr(self, '_text_change_timer'):
            self._text_change_timer.stop()
        
        # Disconnect signals
        try:
            self.editor.textChanged.disconnect(self._on_text_changed)
        except Exception:
            pass

        # Clear saved text
        self._saved_text = None

        # Clear main window reference
        self._main_window = None

        # Delete widget
        self.deleteLater()
        
        gc.collect()

class MarkdownTab(QWidget):
    """Tab widget for Markdown editing with live preview"""
    
    def __init__(self, file_path=None):
        super().__init__()
        self.file_path = file_path
        self._saved_text = ""
        self._is_loading = True
        self._last_preview_text = ""
        self._preview_cache = {}

        # Register cache with memory manager
        memory_manager.register_cache(self._preview_cache, max_size=30)

        # Cache parser instances (must initialize before first update)
        self._markdown_it = None
        self._markdown = None
        self._markdown2 = None

        # Debounce preview updates
        self._preview_timer = QTimer()
        self._preview_timer.setSingleShot(True)
        self._preview_timer.timeout.connect(self._update_preview_debounced)

        # Editor
        self.editor = CodeEditor()

        # Preview
        try:
            from PyQt5.QtWebEngineWidgets import QWebEngineView
            self.preview = QWebEngineView()
            self._use_webengine = True
        except ImportError:
            self.preview = QTextEdit()
            self.preview.setReadOnly(True)
            self.preview.setStyleSheet("background-color: #1e1e1e; color: #e0e0e0; padding: 8px;")
            self._use_webengine = False

        # Layout
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.addWidget(self.editor)
        splitter.addWidget(self.preview)
        splitter.setSizes([600, 400])
        
        # Make splitter handle visible
        splitter.setHandleWidth(1)
        splitter.setStyleSheet("""
            QSplitter::handle {
                background: #30363d;
                border: 1px solid #21262d;
            }
            QSplitter::handle:hover {
                background: #1f6feb;
            }
        """)

        layout = QHBoxLayout(self)
        layout.addWidget(splitter)

        # Connect file worker signals
        file_worker.file_loaded.connect(self._on_file_loaded)
        file_worker.file_error.connect(self._on_file_error)

        # Load file if given
        if file_path:
            self._is_loading = True
            file_worker.load_file(file_path)
        else:
            self._is_loading = False

        # Connect signals after setting text
        self.editor.textChanged.connect(self._on_text_changed)
        self.editor.textChanged.connect(self._trigger_preview_update)

        # Initialize preview
        if not self._is_loading:
            self.update_preview()
    
    def _on_file_loaded(self, file_path, content):
        """Handle file loaded signal from worker thread"""
        if file_path == self.file_path:
            self._saved_text = content
            self.editor.setPlainText(content)
            self._is_loading = False
            self.update_preview()
    
    def _on_file_error(self, file_path, error):
        """Handle file error signal from worker thread"""
        if file_path == self.file_path:
            self.editor.setPlainText(f"Error opening file: {error}")
            self._is_loading = False
    
    def _trigger_preview_update(self):
        """Trigger preview update with debouncing"""
        if not self._is_loading:
            self._preview_timer.start(300)  # 300ms debounce

    def set_layout_mode(self, mode):
        layout = self.layout()
        if not layout:
            return
        # Remove all widgets
        while layout.count():
            item = layout.takeAt(0)
            if item:
                widget = item.widget()
                if widget:
                    widget.setParent(None)

        # Defensive: recreate QTextEdit if needed
        if not hasattr(self.preview, "setReadOnly") or not self.preview:
            from PyQt5.QtWidgets import QTextEdit
            self.preview = QTextEdit()
            self.preview.setReadOnly(True)
            self.preview.setStyleSheet("background-color: #1e1e1e; color: #e0e0e0; padding: 8px;")

        # Apply layout
        if mode == "Horizontal Split":
            splitter = QSplitter(Qt.Orientation.Horizontal)
        elif mode == "Vertical Split":
            splitter = QSplitter(Qt.Orientation.Vertical)
        else:
            splitter = None

        if splitter:
            splitter.addWidget(self.editor)
            splitter.addWidget(self.preview)
            splitter.setSizes([600, 400] if mode == "Horizontal Split" else [400, 400])
            
            # Make splitter handle visible
            splitter.setHandleWidth(1)
            splitter.setStyleSheet("""
                QSplitter::handle {
                    background: #30363d;
                    border: 1px solid #21262d;
                }
                QSplitter::handle:hover {
                    background: #1f6feb;
                }
            """)
            
            layout.addWidget(splitter)
        elif mode == "Editor Only":
            layout.addWidget(self.editor)
        elif mode == "Preview Only":
            layout.addWidget(self.preview)

    def is_modified(self):
        return self.editor.toPlainText() != self._saved_text

    def mark_saved(self):
        self._saved_text = self.editor.toPlainText()

    def _on_text_changed(self):
        mw = self.parent().parent() if self.parent() else None
        if mw and hasattr(mw, "update_tab_title_modified"):
            mw.update_tab_title_modified(self)

    def _update_preview_debounced(self):
        """Debounced preview update"""
        self.update_preview()
    
    def update_preview(self):
        """Update markdown preview"""
        text = self.editor.toPlainText()
        
        if text == self._last_preview_text:
            return

        if text in self._preview_cache:
            html = self._preview_cache[text]
        else:
            html = self._render_markdown_to_html(text)
            if len(self._preview_cache) > 50:
                oldest_key = next(iter(self._preview_cache))
                del self._preview_cache[oldest_key]
            self._preview_cache[text] = html

        self._last_preview_text = text

        try:
            if self._use_webengine:
                from PyQt5.QtCore import QUrl
                base_url = QUrl.fromLocalFile(os.path.dirname(self.file_path) + "/") if self.file_path else QUrl()
                self.preview.setHtml(html, base_url)
            else:
                self.preview.setHtml(html)
        except Exception as e:
            if hasattr(self.preview, 'setPlainText'):
                self.preview.setPlainText(text)


    def _render_markdown_to_html(self, text):
        # Filter out comment lines starting with !!
        filtered_lines = []
        for line in text.split('\n'):
            if not line.strip().startswith('!!'):
                filtered_lines.append(line)
        text = '\n'.join(filtered_lines)
        
        # CSS/JS
        katex_head = '''
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
    <script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
    <script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/contrib/auto-render.min.js"
    onload="renderMathInElement(document.body, {delimiters: [
        {left: '$$', right: '$$', display: true},
        {left: '$', right: '$', display: false}
    ]});"></script>
    '''
        github_css = '''
    <style>
    body { 
        background: #0d1117; 
        color: #e6edf3; 
        font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', 'Noto Sans', Helvetica, Arial, sans-serif;
        line-height: 1.6;
        margin: 0; 
        padding: 24px;
        font-size: 16px;
    }
    .markdown-body { 
        background: #0d1117; 
        color: #e6edf3; 
        padding: 24px; 
        border-radius: 6px;
        max-width: 980px;
        margin: 0 auto;
    }
    pre, code { 
        background: #161b22; 
        color: #e6edf3; 
        border-radius: 6px;
        border: 1px solid #30363d;
        font-family: 'JetBrains Mono', 'Fira Code', 'Consolas', monospace;
    }
    pre { 
        padding: 16px; 
        overflow: auto;
        line-height: 1.45;
    }
    code {
        padding: 0.2em 0.4em;
        font-size: 85%;
    }
    table { 
        border-collapse: collapse; 
        width: 100%;
        margin: 16px 0;
    }
    th, td { 
        border: 1px solid #30363d; 
        padding: 8px 16px;
        text-align: left;
    }
    th { 
        background: #161b22;
        font-weight: 600;
    }
    tr:nth-child(2n) { 
        background: #0d1117;
    }
    tr:hover {
        background: #161b22;
    }
    h1, h2, h3, h4, h5, h6 {
        color: #58a6ff;
        font-weight: 600;
        line-height: 1.25;
        margin-top: 24px;
        margin-bottom: 16px;
    }
    h1 { 
        font-size: 2em; 
        border-bottom: 1px solid #21262d;
        padding-bottom: 0.3em;
    }
    h2 { 
        font-size: 1.5em; 
        border-bottom: 1px solid #21262d;
        padding-bottom: 0.3em;
    }
    h3 { font-size: 1.25em; }
    h4 { font-size: 1em; }
    h5 { font-size: 0.875em; }
    h6 { font-size: 0.85em; color: #8b949e; }
    
    a { 
        color: #58a6ff; 
        text-decoration: none;
        font-weight: 500;
    }
    a:hover { 
        text-decoration: underline; 
    }
    
    blockquote { 
        color: #8b949e; 
        border-left: 4px solid #30363d; 
        padding-left: 16px; 
        margin: 16px 0;
        font-style: italic;
    }
    
    ul, ol { 
        padding-left: 2em;
        margin: 16px 0;
    }
    li {
        margin: 8px 0;
    }
    
    input[type=checkbox] { 
        accent-color: #58a6ff;
        margin-right: 8px;
    }
    
    del { 
        color: #f85149;
        text-decoration: line-through;
    }
    
    .task-list-item { 
        list-style-type: none;
        margin-left: -1.5em;
    }
    
    dl { 
        margin: 16px 0;
    }
    dt { 
        font-weight: 600;
        margin-top: 16px;
    }
    dd { 
        margin-left: 2em;
        margin-bottom: 16px;
    }
    
    strong { 
        color: #f0883e;
        font-weight: 600;
    }
    
    em { 
        color: #d2a8ff;
        font-style: italic;
    }
    
    strong em, em strong { 
        color: #ff7b72;
        font-weight: 600;
        font-style: italic;
    }
    
    img { 
        max-width: 100%; 
        height: auto; 
        display: block; 
        margin: 16px 0;
        border-radius: 6px;
        border: 1px solid #30363d;
    }
    
    hr {
        height: 2px;
        padding: 0;
        margin: 24px 0;
        background-color: #21262d;
        border: 0;
    }
    
    p {
        margin-top: 0;
        margin-bottom: 16px;
    }
    
    /* GitHub-style Alerts/Annotations */
    blockquote.alert {
        border-left-width: 4px;
        border-radius: 6px;
        padding: 12px 16px;
        margin: 16px 0;
        font-style: normal;
        background: #161b22;
    }
    
    /* Note - Blue */
    blockquote.alert-note {
        border-left-color: #58a6ff;
        background: rgba(88, 166, 255, 0.1);
    }
    blockquote.alert-note::before {
        content: "Note";
        display: block;
        font-weight: 600;
        color: #58a6ff;
        margin-bottom: 8px;
    }
    
    /* Tip - Green */
    blockquote.alert-tip {
        border-left-color: #3fb950;
        background: rgba(63, 185, 80, 0.1);
    }
    blockquote.alert-tip::before {
        content: "Tip";
        display: block;
        font-weight: 600;
        color: #3fb950;
        margin-bottom: 8px;
    }
    
    /* Important - Purple */
    blockquote.alert-important {
        border-left-color: #a371f7;
        background: rgba(163, 113, 247, 0.1);
    }
    blockquote.alert-important::before {
        content: "Important";
        display: block;
        font-weight: 600;
        color: #a371f7;
        margin-bottom: 8px;
    }
    
    /* Warning - Orange */
    blockquote.alert-warning {
        border-left-color: #d29922;
        background: rgba(210, 153, 34, 0.1);
    }
    blockquote.alert-warning::before {
        content: "Warning";
        display: block;
        font-weight: 600;
        color: #d29922;
        margin-bottom: 8px;
    }
    
    /* Caution/Danger - Red */
    blockquote.alert-caution {
        border-left-color: #f85149;
        background: rgba(248, 81, 73, 0.1);
    }
    blockquote.alert-caution::before {
        content: "Caution";
        display: block;
        font-weight: 600;
        color: #f85149;
        margin-bottom: 8px;
    }
    
    blockquote.alert p:last-child {
        margin-bottom: 0;
    }
    
    /* Custom Scrollbar Styling for WebView */
    ::-webkit-scrollbar {
        width: 10px;
        height: 10px;
    }

    ::-webkit-scrollbar-track {
        background: #0d1117;
    }

    ::-webkit-scrollbar-thumb {
        background: #30363d;
    }

    
    ::-webkit-scrollbar-thumb:hover {
        background: #484f58;
    }
    
    ::-webkit-scrollbar-thumb:active {
        background: #58a6ff;
    }
    
    ::-webkit-scrollbar-corner {
        background: #0d1117;
    }
    </style>
    '''

        html_body = None

        # Try markdown-it-py
        if not self._markdown_it:
            try:
                from markdown_it import MarkdownIt
                from mdit_py_plugins.footnote import footnote_plugin
                from mdit_py_plugins.tasklists import tasklists_plugin
                from mdit_py_plugins.emoji import emoji_plugin
                from mdit_py_plugins.attrs import attrs_plugin
                from mdit_py_plugins.deflist import deflist_plugin
                from mdit_py_plugins.texmath import math_plugin
                self._markdown_it = (
                    MarkdownIt("gfm", {"html": True, "linkify": True, "typographer": True})
                    .use(footnote_plugin)
                    .use(tasklists_plugin)
                    .use(emoji_plugin)
                    .use(attrs_plugin)
                    .use(deflist_plugin)
                    .use(math_plugin, {"engine": "katex", "inlineRenderer": "katex", "blockRenderer": "katex"})
                )
            except ImportError:
                self._markdown_it = None

        if self._markdown_it:
            try:
                html_body = self._markdown_it.render(text)
            except Exception:
                html_body = None

        # Fallbacks
        if not html_body:
            if not self._markdown:
                try:
                    import markdown as md
                    self._markdown = md
                except ImportError:
                    self._markdown = None
            if self._markdown:
                html_body = self._markdown.markdown(text, extensions=['extra','tables','fenced_code'], output_format='html')

        if not html_body:
            if not self._markdown2:
                try:
                    import markdown2
                    self._markdown2 = markdown2
                except ImportError:
                    self._markdown2 = None
            if self._markdown2:
                html_body = self._markdown2.markdown(text, extras=['fenced-code-blocks','tables'])

        if not html_body:
            return "<b>Markdown preview requires a markdown parser.</b>"
        
        # Add JavaScript to process GitHub-style alerts
        alert_script = '''
        <script>
        document.addEventListener('DOMContentLoaded', function() {
            // Process all blockquotes for GitHub-style alerts
            document.querySelectorAll('blockquote').forEach(function(blockquote) {
                // Check if blockquote contains multiple paragraphs (multiple alerts)
                var paragraphs = blockquote.querySelectorAll('p');
                
                if (paragraphs.length > 1) {
                    // Multiple paragraphs - need to split into separate blockquotes
                    var parent = blockquote.parentNode;
                    var nextSibling = blockquote.nextSibling;
                    
                    paragraphs.forEach(function(p) {
                        var text = p.textContent.trim();
                        var alertType = null;
                        var newContent = null;
                        
                        // Check for alert patterns
                        if (text.match(/^N:/i) || text.match(/^NOTE:/i)) {
                            alertType = 'alert-note';
                            newContent = text.replace(/^(N:|NOTE:)\s*/i, '');
                        }
                        else if (text.match(/^T:/i) || text.match(/^TIP:/i)) {
                            alertType = 'alert-tip';
                            newContent = text.replace(/^(T:|TIP:)\s*/i, '');
                        }
                        else if (text.match(/^W:/i) || text.match(/^WARNING:/i)) {
                            alertType = 'alert-warning';
                            newContent = text.replace(/^(W:|WARNING:)\s*/i, '');
                        }
                        else if (text.match(/^I:/i) || text.match(/^IMPORTANT:/i)) {
                            alertType = 'alert-important';
                            newContent = text.replace(/^(I:|IMPORTANT:)\s*/i, '');
                        }
                        else if (text.match(/^C:/i) || text.match(/^CAUTION:/i)) {
                            alertType = 'alert-caution';
                            newContent = text.replace(/^(C:|CAUTION:)\s*/i, '');
                        }
                        
                        if (alertType) {
                            // Create new blockquote for this alert
                            var newBlockquote = document.createElement('blockquote');
                            newBlockquote.classList.add('alert', alertType);
                            var newP = document.createElement('p');
                            newP.innerHTML = newContent;
                            newBlockquote.appendChild(newP);
                            parent.insertBefore(newBlockquote, nextSibling);
                        } else {
                            // Keep as regular blockquote
                            var newBlockquote = document.createElement('blockquote');
                            newBlockquote.appendChild(p.cloneNode(true));
                            parent.insertBefore(newBlockquote, nextSibling);
                        }
                    });
                    
                    // Remove original blockquote
                    parent.removeChild(blockquote);
                } else {
                    // Single paragraph blockquote - process normally
                    var firstChild = blockquote.firstElementChild;
                    if (!firstChild) return;
                    
                    var text = firstChild.textContent.trim();
                    var alertType = null;
                    var newContent = null;
                    
                    // Check for alert patterns
                    if (text.match(/^N:/i) || text.match(/^NOTE:/i)) {
                        alertType = 'alert-note';
                        newContent = text.replace(/^(N:|NOTE:)\s*/i, '');
                    }
                    else if (text.match(/^T:/i) || text.match(/^TIP:/i)) {
                        alertType = 'alert-tip';
                        newContent = text.replace(/^(T:|TIP:)\s*/i, '');
                    }
                    else if (text.match(/^W:/i) || text.match(/^WARNING:/i)) {
                        alertType = 'alert-warning';
                        newContent = text.replace(/^(W:|WARNING:)\s*/i, '');
                    }
                    else if (text.match(/^I:/i) || text.match(/^IMPORTANT:/i)) {
                        alertType = 'alert-important';
                        newContent = text.replace(/^(I:|IMPORTANT:)\s*/i, '');
                    }
                    else if (text.match(/^C:/i) || text.match(/^CAUTION:/i)) {
                        alertType = 'alert-caution';
                        newContent = text.replace(/^(C:|CAUTION:)\s*/i, '');
                    }
                    
                    // Apply the alert styling
                    if (alertType) {
                        blockquote.classList.add('alert', alertType);
                        firstChild.innerHTML = newContent;
                    }
                }
            });
        });
        </script>
        '''

        return f"<!DOCTYPE html><html><head>{katex_head}{github_css}{alert_script}</head><body class='markdown-body'>{html_body}</body></html>"

    def close_tab(self):
        # Stop timers
        if hasattr(self, '_preview_timer'):
            self._preview_timer.stop()
        
        # Disconnect signals
        try:
            self.editor.textChanged.disconnect(self._trigger_preview_update)
            self.editor.textChanged.disconnect(self._on_text_changed)
        except Exception:
            pass

        # Clear cached markdown parsers
        self._markdown_it = None
        self._markdown = None
        self._markdown2 = None
        
        # Clear caches
        self._preview_cache.clear()
        self._last_preview_text = ""

        # Delete the widget itself
        self.deleteLater()

        gc.collect()

class PDFTab(QWidget):
    """Tab widget for viewing PDF files with zoom and navigation"""
    
    def __init__(self, file_path):
        super().__init__()
        self.file_path: str = file_path
        self.zoom_factor: float = 2
        self.min_zoom: int = 1
        self.max_zoom: int = 5
        self.cache: Dict[tuple, QPixmap] = {}
        self._max_cache_size: int = 20  # Limit cache size
        self._rendering_in_progress: bool = False
        self.scroll: QScrollArea

        self.main_layout = QVBoxLayout(self)
        self.setLayout(self.main_layout)

        if not os.path.exists(file_path):
            label = QLabel("<b>PDF file not found.</b>")
            label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            self.main_layout.addWidget(label)
            return

        try:
            self.doc = fitz.open(file_path)

            # Page indicator
            self.page_indicator = QLabel()
            self.page_indicator.setAlignment(Qt.AlignmentFlag.AlignCenter)
            self.page_indicator.setFixedHeight(25)
            self.main_layout.addWidget(self.page_indicator)

            # Page jump layout
            jump_layout = QHBoxLayout()
            jump_layout.addStretch()
            jump_layout.addWidget(QLabel("Go to page:"))
            self.page_input = QLineEdit()
            self.page_input.setFixedWidth(50)
            self.page_input.setPlaceholderText("Page #")
            self.page_input.returnPressed.connect(self.go_to_page)
            jump_layout.addWidget(self.page_input)
            self.go_button = QPushButton("Go")
            self.go_button.clicked.connect(self.go_to_page)
            jump_layout.addWidget(self.go_button)
            jump_layout.addStretch()
            self.main_layout.addLayout(jump_layout)

            # Scroll area for pages
            self.scroll = QScrollArea()
            self.scroll.setWidgetResizable(True)
            self.content_widget = QWidget()
            self.content_layout = QVBoxLayout(self.content_widget)
            self.content_layout.setContentsMargins(0, 0, 0, 0)
            self.content_layout.setSpacing(10)
            self.page_labels = []
            for _ in range(len(self.doc)):
                label = QLabel("Loading...")
                label.setAlignment(Qt.AlignmentFlag.AlignCenter)
                label.setMinimumHeight(100)
                self.content_layout.addWidget(label)
                self.page_labels.append(label)
            self.scroll.setWidget(self.content_widget)
            self.main_layout.addWidget(self.scroll)

            # Zoom buttons
            btn_layout = QHBoxLayout()
            btn_layout.addStretch()
            self.zoom_out_btn = QPushButton("–")
            self.zoom_out_btn.setFixedWidth(30)
            self.zoom_out_btn.clicked.connect(self.zoom_out)
            btn_layout.addWidget(self.zoom_out_btn)
            self.zoom_in_btn = QPushButton("+")
            self.zoom_in_btn.setFixedWidth(30)
            self.zoom_in_btn.clicked.connect(self.zoom_in)
            btn_layout.addWidget(self.zoom_in_btn)
            self.main_layout.addLayout(btn_layout)

            # Scroll timer
            self.scroll_timer = QTimer()
            self.scroll_timer.setInterval(200)
            self.scroll_timer.setSingleShot(True)
            self.scroll_timer.timeout.connect(self.on_scroll_idle)
            scrollbar = self.scroll.verticalScrollBar()
            if scrollbar:
                scrollbar.valueChanged.connect(self.on_scroll)

            # Initial render
            QTimer.singleShot(0, self.render_visible_pages)
            self.update_page_indicator(1)

        except Exception as e:
            label = QLabel(f"<b>Failed to render PDF:</b><br>{e}")
            label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            self.main_layout.addWidget(label)
            btn = QPushButton("Open in system viewer")
            btn.clicked.connect(lambda: self.open_external(file_path))
            self.main_layout.addWidget(btn)

    # ----------------- Page Navigation -----------------
    def go_to_page(self):
        text = self.page_input.text().strip()
        if not text.isdigit():
            QMessageBox.warning(self, "Invalid Input", "Please enter a valid page number.")
            return
        page_num = int(text)
        if page_num < 1 or page_num > len(self.doc):
            QMessageBox.warning(self, "Out of Range", f"Please enter a page number between 1 and {len(self.doc)}.")
            return
        label = self.page_labels[page_num - 1]
        scrollbar = self.scroll.verticalScrollBar()
        if scrollbar:
            scrollbar.setValue(label.y())
        self.update_page_indicator(page_num)

    # ----------------- Scroll Handling -----------------
    def on_scroll(self):
        self.update_current_page()
        self.scroll_timer.start()

    def on_scroll_idle(self):
        self.render_visible_pages()

    # ----------------- Rendering -----------------
    def render_visible_pages(self):
        if self._rendering_in_progress:
            return
        
        self._rendering_in_progress = True
        
        try:
            viewport = self.scroll.viewport()
            scrollbar = self.scroll.verticalScrollBar()
            if not viewport or not scrollbar:
                self._rendering_in_progress = False
                return
            visible_rect = QRect(
                0,
                scrollbar.value(),
                viewport.width(),
                viewport.height()
            )

            for page_number, label in enumerate(self.page_labels):
                label_y = label.y()
                label_height = label.height()
                if label_y + label_height >= visible_rect.y() and label_y <= visible_rect.y() + visible_rect.height():
                    key = (page_number, self.zoom_factor)
                    if key in self.cache:
                        pixmap = self.cache[key]
                    else:
                        # Limit cache size
                        if len(self.cache) >= self._max_cache_size:
                            # Remove oldest entries
                            oldest_key = next(iter(self.cache))
                            del self.cache[oldest_key]
                        
                        page = self.doc.load_page(page_number)
                        zoom_matrix = fitz.Matrix(self.zoom_factor, self.zoom_factor)
                        pix = page.get_pixmap(matrix=zoom_matrix)
                        fmt = QImage.Format_RGBA8888 if pix.alpha else QImage.Format_RGB888
                        image = QImage(pix.samples, pix.width, pix.height, pix.stride, fmt)
                        pixmap = QPixmap.fromImage(image)
                        self.cache[key] = pixmap
                    label.setPixmap(pixmap)
                    label.setMinimumHeight(pixmap.height())
                    label.setMinimumWidth(pixmap.width())
                    label.setText("")
                else:
                    if label.pixmap():
                        label.setPixmap(QPixmap())  # free memory
                    label.setText("Loading...")
        finally:
            self._rendering_in_progress = False

    # ----------------- Current Page Indicator -----------------
    def update_current_page(self):
        scrollbar = self.scroll.verticalScrollBar()
        viewport = self.scroll.viewport()
        if not scrollbar or not viewport:
            return
        scrollbar_val = scrollbar.value()
        viewport_middle = scrollbar_val + viewport.height() // 2
        current_page, min_distance = 1, None
        for i, label in enumerate(self.page_labels):
            label_center = label.y() + label.height() // 2
            distance = abs(label_center - viewport_middle)
            if min_distance is None or distance < min_distance:
                min_distance = distance
                current_page = i + 1
        self.update_page_indicator(current_page)

    def update_page_indicator(self, page_number):
        self.page_indicator.setText(f"Page {page_number} of {len(self.doc)}")

    # ----------------- Zoom -----------------
    def zoom_in(self):
        if self.zoom_factor < self.max_zoom:
            self.zoom_factor += 0.5
            self._clear_cache()
            self.render_visible_pages()

    def zoom_out(self):
        if self.zoom_factor > self.min_zoom:
            self.zoom_factor -= 0.5
            self._clear_cache()
            self.render_visible_pages()

    def _clear_cache(self):
        for pixmap in self.cache.values():
            pixmap.detach()
            del pixmap
        self.cache.clear()
        gc.collect()

    # ----------------- External Viewer -----------------
    def open_external(self, file_path):
        import sys, subprocess
        if sys.platform.startswith('win'):
            os.startfile(file_path)
        elif sys.platform.startswith('darwin'):
            subprocess.Popen(['open', file_path])
        else:
            subprocess.Popen(['xdg-open', file_path])

    # ----------------- Full Cleanup -----------------
    def close_tab(self):
        # Stop timers
        if hasattr(self, 'scroll_timer'):
            self.scroll_timer.stop()
            try:
                self.scroll_timer.timeout.disconnect()
            except Exception:
                pass
            del self.scroll_timer

        # Disconnect scroll
        if hasattr(self, 'scroll') and self.scroll:
            try:
                scrollbar = self.scroll.verticalScrollBar()
                if scrollbar:
                    scrollbar.valueChanged.disconnect()
            except Exception:
                pass

        # Clear cache and pixmaps
        self._clear_cache()

        # Delete labels
        for label in getattr(self, 'page_labels', []):
            label.clear()
            label.deleteLater()
        self.page_labels.clear()

        # Clear layouts
        def clear_layout(layout):
            if layout is not None:
                while layout.count():
                    item = layout.takeAt(0)
                    if item:
                        w = item.widget()
                        if w is not None:
                            w.deleteLater()
        clear_layout(self.content_layout)
        clear_layout(self.main_layout)

        # Delete content widget
        if hasattr(self, 'content_widget'):
            self.content_widget.deleteLater()

        # Delete self
        self.deleteLater()
        gc.collect()

class ImageTab(QWidget):
    """Tab widget for viewing images with zoom support"""
    
    def __init__(self, file_path):
        super().__init__()
        self.file_path = file_path
        self.scale_factor = 1.0
        self.base_pixmap = None

        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Scroll Area
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)

        # Image Label
        self.label = QLabel()
        self.label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.scroll_area.setWidget(self.label)
        layout.addWidget(self.scroll_area)

        # Load Pixmap
        try:
            pixmap = QPixmap(file_path)
            if pixmap.isNull():
                self.label.setText("<b>Could not load image.</b>")
            else:
                self.base_pixmap = pixmap
                self.update_pixmap()
        except Exception as e:
            self.label.setText(f"<b>Error loading image:</b> {e}")

    def update_pixmap(self):
        """Rescale and display the pixmap according to current zoom factor."""
        if self.base_pixmap:
            scaled = self.base_pixmap.scaled(
                int(self.base_pixmap.width() * self.scale_factor),
                int(self.base_pixmap.height() * self.scale_factor),
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation
            )
            self.label.setPixmap(scaled)

    def wheelEvent(self, a0):
        """Zoom in/out with Ctrl + Scroll."""
        if a0 and a0.modifiers() & Qt.KeyboardModifier.ControlModifier:
            if a0.angleDelta().y() > 0:  # scroll up
                self.scale_factor *= 1.1
            else:  # scroll down
                self.scale_factor /= 1.1

            # Clamp zoom
            self.scale_factor = max(0.1, min(self.scale_factor, 10.0))
            self.update_pixmap()
            a0.accept()
        else:
            super().wheelEvent(a0)

    # ----------------- Full Cleanup -----------------
    def close_tab(self):
        # Remove pixmap references
        if self.label:
            self.label.clear()
            self.label.deleteLater()
        if self.base_pixmap:
            del self.base_pixmap
            self.base_pixmap = None

        # Remove scroll area
        if self.scroll_area:
            self.scroll_area.deleteLater()
            self.scroll_area = None

        # Remove layout
        layout = self.layout()
        if layout:
            while layout.count():
                item = layout.takeAt(0)
                if item:
                    widget = item.widget()
                    if widget:
                        widget.deleteLater()
            layout.deleteLater()

        # Delete self
        self.deleteLater()
        gc.collect()

class AssetBrowserTab(QWidget):
    """Enhanced visual asset browser for image-heavy folders"""
    def __init__(self, folder_path):
        super().__init__()
        self.folder_path = folder_path
        self.thumbnails = []
        self.current_preview = None
        self.all_files = []
        self.filtered_files = []
        self.view_mode = 'grid'  # 'grid' or 'list'
        self.sort_mode = 'name'  # 'name', 'size', 'date', 'type'
        self.filter_type = 'all'  # 'all', 'images', 'videos', 'audio', 'documents'
        self.thumbnail_size = 150
        
        # Main layout
        main_layout = QHBoxLayout(self)
        
        # Left side: Asset grid/list
        left_widget = QWidget()
        left_layout = QVBoxLayout(left_widget)
        
        # Header with stats
        header_widget = QWidget()
        header_layout = QHBoxLayout(header_widget)
        header_layout.setContentsMargins(0, 0, 0, 0)
        
        self.header_label = QLabel(f"🎨 Assets Browser")
        self.header_label.setStyleSheet("""
            font-size: 18px;
            font-weight: bold;
            color: #58a6ff;
        """)
        header_layout.addWidget(self.header_label)
        
        self.stats_label = QLabel()
        self.stats_label.setStyleSheet("""
            color: #8b949e;
            font-size: 12px;
            padding: 5px;
        """)
        header_layout.addWidget(self.stats_label)
        header_layout.addStretch()
        
        header_frame = QFrame()
        header_frame.setStyleSheet("""
            QFrame {
                background: #161b22;
                border-radius: 6px;
                padding: 10px;
            }
        """)
        header_frame_layout = QVBoxLayout(header_frame)
        header_frame_layout.setContentsMargins(10, 10, 10, 10)
        header_frame_layout.addWidget(header_widget)
        left_layout.addWidget(header_frame)
        
        # Toolbar
        toolbar = QWidget()
        toolbar_layout = QHBoxLayout(toolbar)
        toolbar_layout.setContentsMargins(0, 5, 0, 5)
        
        # Search box
        self.search_box = QLineEdit()
        self.search_box.setPlaceholderText("🔍 Search assets...")
        self.search_box.setStyleSheet("""
            QLineEdit {
                background: #0d1117;
                border: 1px solid #30363d;
                border-radius: 6px;
                padding: 8px 12px;
                color: #e6edf3;
                font-size: 13px;
            }
            QLineEdit:focus {
                border-color: #1f6feb;
            }
        """)
        self.search_box.textChanged.connect(self.filter_assets)
        toolbar_layout.addWidget(self.search_box, 1)
        
        # Filter by type
        type_label = QLabel("Type:")
        type_label.setStyleSheet("color: #8b949e; font-size: 12px;")
        toolbar_layout.addWidget(type_label)
        
        self.type_combo = QComboBox()
        self.type_combo.addItems(["All", "Images", "Videos", "Audio", "Documents", "Other"])
        self.type_combo.setStyleSheet("""
            QComboBox {
                background: #0d1117;
                border: 1px solid #30363d;
                border-radius: 4px;
                padding: 6px 10px;
                color: #e6edf3;
                min-width: 100px;
            }
        """)
        self.type_combo.currentTextChanged.connect(self.filter_by_type)
        toolbar_layout.addWidget(self.type_combo)
        
        # Sort options
        sort_label = QLabel("Sort:")
        sort_label.setStyleSheet("color: #8b949e; font-size: 12px;")
        toolbar_layout.addWidget(sort_label)
        
        self.sort_combo = QComboBox()
        self.sort_combo.addItems(["Name", "Size", "Date", "Type"])
        self.sort_combo.setStyleSheet("""
            QComboBox {
                background: #0d1117;
                border: 1px solid #30363d;
                border-radius: 4px;
                padding: 6px 10px;
                color: #e6edf3;
                min-width: 80px;
            }
        """)
        self.sort_combo.currentTextChanged.connect(self.sort_assets)
        toolbar_layout.addWidget(self.sort_combo)
        
        # View mode toggle
        view_group = QWidget()
        view_layout = QHBoxLayout(view_group)
        view_layout.setContentsMargins(0, 0, 0, 0)
        view_layout.setSpacing(5)
        
        self.grid_btn = QPushButton("🔲")
        self.grid_btn.setToolTip("Grid View")
        self.grid_btn.setCheckable(True)
        self.grid_btn.setChecked(True)
        self.grid_btn.clicked.connect(lambda: self.change_view_mode('grid'))
        self.grid_btn.setStyleSheet("""
            QPushButton {
                background: #238636;
                border: none;
                padding: 6px 12px;
                border-radius: 4px;
                color: white;
                font-size: 14px;
            }
            QPushButton:hover {
                background: #2ea043;
            }
            QPushButton:!checked {
                background: #21262d;
            }
        """)
        
        self.list_btn = QPushButton("☰")
        self.list_btn.setToolTip("List View")
        self.list_btn.setCheckable(True)
        self.list_btn.clicked.connect(lambda: self.change_view_mode('list'))
        self.list_btn.setStyleSheet(self.grid_btn.styleSheet())
        
        view_layout.addWidget(self.grid_btn)
        view_layout.addWidget(self.list_btn)
        toolbar_layout.addWidget(view_group)
        
        # Thumbnail size slider (only for grid view)
        self.size_slider = QSlider(Qt.Orientation.Horizontal)
        self.size_slider.setMinimum(100)
        self.size_slider.setMaximum(250)
        self.size_slider.setValue(150)
        self.size_slider.setFixedWidth(100)
        self.size_slider.valueChanged.connect(self.change_thumbnail_size)
        self.size_slider.setStyleSheet("""
            QSlider::groove:horizontal {
                border: 1px solid #30363d;
                height: 4px;
                background: #21262d;
                border-radius: 2px;
            }
            QSlider::handle:horizontal {
                background: #58a6ff;
                width: 14px;
                height: 14px;
                margin: -5px 0;
                border-radius: 7px;
            }
        """)
        toolbar_layout.addWidget(QLabel("Size:"))
        toolbar_layout.addWidget(self.size_slider)
        
        left_layout.addWidget(toolbar)
        
        # Scroll area for assets
        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setStyleSheet("""
            QScrollArea {
                border: none;
                background: #0d1117;
            }
        """)
        
        # Container widget for grid/list
        self.container_widget = QWidget()
        self.grid_layout = QGridLayout(self.container_widget)
        self.grid_layout.setSpacing(15)
        self.grid_layout.setContentsMargins(10, 10, 10, 10)
        
        self.scroll.setWidget(self.container_widget)
        left_layout.addWidget(self.scroll)
        
        # Right side: Enhanced Preview panel
        right_widget = QFrame()
        right_widget.setStyleSheet("""
            QFrame {
                background: #161b22;
                border-radius: 8px;
                border: 1px solid #30363d;
            }
        """)
        right_widget.setMinimumWidth(350)
        right_layout = QVBoxLayout(right_widget)
        
        preview_header = QLabel("📋 Asset Details")
        preview_header.setStyleSheet("""
            font-size: 16px;
            font-weight: bold;
            color: #e6edf3;
            padding: 10px;
        """)
        right_layout.addWidget(preview_header)
        
        # Preview image
        self.preview_label = QLabel()
        self.preview_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.preview_label.setStyleSheet("""
            QLabel {
                background: #0d1117;
                border-radius: 6px;
                padding: 20px;
                min-width: 300px;
            }
        """)
        self.preview_label.setText("Select an asset to preview")
        right_layout.addWidget(self.preview_label, 1)
        
        # File info
        self.info_label = QLabel()
        self.info_label.setStyleSheet("""
            QLabel {
                color: #8b949e;
                padding: 10px;
                font-size: 12px;
            }
        """)
        self.info_label.setWordWrap(True)
        right_layout.addWidget(self.info_label)
        
        # Action buttons
        actions_widget = QWidget()
        actions_layout = QVBoxLayout(actions_widget)
        actions_layout.setSpacing(8)
        
        self.open_btn = QPushButton("📂 Open in Editor")
        self.open_btn.setStyleSheet("""
            QPushButton {
                background: #238636;
                color: white;
                border: none;
                padding: 10px 20px;
                border-radius: 6px;
                font-weight: bold;
            }
            QPushButton:hover {
                background: #2ea043;
            }
            QPushButton:disabled {
                background: #21262d;
                color: #6e7681;
            }
        """)
        self.open_btn.clicked.connect(self.open_in_editor)
        self.open_btn.setEnabled(False)
        actions_layout.addWidget(self.open_btn)
        
        self.copy_path_btn = QPushButton("📋 Copy Path")
        self.copy_path_btn.setStyleSheet("""
            QPushButton {
                background: #1f6feb;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 6px;
                font-weight: 500;
            }
            QPushButton:hover {
                background: #388bfd;
            }
            QPushButton:disabled {
                background: #21262d;
                color: #6e7681;
            }
        """)
        self.copy_path_btn.clicked.connect(self.copy_path)
        self.copy_path_btn.setEnabled(False)
        actions_layout.addWidget(self.copy_path_btn)
        
        self.reveal_btn = QPushButton("👁️ Reveal in Explorer")
        self.reveal_btn.setStyleSheet("""
            QPushButton {
                background: #6e7681;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 6px;
                font-weight: 500;
            }
            QPushButton:hover {
                background: #8b949e;
            }
            QPushButton:disabled {
                background: #21262d;
                color: #6e7681;
            }
        """)
        self.reveal_btn.clicked.connect(self.reveal_in_explorer)
        self.reveal_btn.setEnabled(False)
        actions_layout.addWidget(self.reveal_btn)
        
        right_layout.addWidget(actions_widget)
        
        # Add to splitter
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.addWidget(left_widget)
        splitter.addWidget(right_widget)
        splitter.setSizes([700, 300])
        
        main_layout.addWidget(splitter)
        
        # Load assets
        self.load_assets()
    
    def load_assets(self):
        """Load all assets from folder and subfolders recursively"""
        if not os.path.exists(self.folder_path):
            return
        
        # Define file categories
        image_exts = ['.png', '.jpg', '.jpeg', '.gif', '.bmp', '.webp', '.svg', '.ico', '.tiff', '.psd']
        video_exts = ['.mp4', '.avi', '.mov', '.wmv', '.flv', '.mkv', '.webm']
        audio_exts = ['.mp3', '.wav', '.ogg', '.m4a', '.flac', '.aac', '.wma']
        doc_exts = ['.pdf', '.doc', '.docx', '.txt', '.md', '.json', '.xml', '.csv']
        
        try:
            # Walk through directory tree recursively
            for root, dirs, files in os.walk(self.folder_path):
                # Skip hidden directories
                dirs[:] = [d for d in dirs if not d.startswith('.')]
                
                for item in files:
                    # Skip hidden files
                    if item.startswith('.'):
                        continue
                    
                    full_path = os.path.join(root, item)
                    ext = os.path.splitext(item)[1].lower()
                    
                    # Categorize file
                    if ext in image_exts:
                        category = 'image'
                    elif ext in video_exts:
                        category = 'video'
                    elif ext in audio_exts:
                        category = 'audio'
                    elif ext in doc_exts:
                        category = 'document'
                    else:
                        category = 'other'
                    
                    # Get file info
                    size = os.path.getsize(full_path)
                    mtime = os.path.getmtime(full_path)
                    
                    # Get relative path for display
                    rel_path = os.path.relpath(full_path, self.folder_path)
                    
                    # Get subfolder name
                    subfolder = os.path.dirname(rel_path)
                    if subfolder == '.':
                        subfolder = 'Root'
                    
                    self.all_files.append({
                        'name': item,
                        'path': full_path,
                        'rel_path': rel_path,
                        'subfolder': subfolder,
                        'ext': ext,
                        'category': category,
                        'size': size,
                        'mtime': mtime
                    })
        except Exception as e:
            print(f"Error loading assets: {e}")
            return
        
        # Initial sort and filter
        self.filtered_files = self.all_files.copy()
        self.sort_assets(self.sort_combo.currentText())
        self.update_stats()
        self.display_assets()
    
    def update_stats(self):
        """Update statistics display"""
        total = len(self.all_files)
        filtered = len(self.filtered_files)
        
        # Calculate total size
        total_size = sum(f['size'] for f in self.filtered_files)
        size_str = self.format_size(total_size)
        
        if filtered == total:
            self.stats_label.setText(f"{total} files • {size_str}")
        else:
            self.stats_label.setText(f"Showing {filtered} of {total} files • {size_str}")
    
    def filter_assets(self):
        """Filter assets based on search text"""
        search_text = self.search_box.text().lower()
        
        if not search_text:
            self.filtered_files = [f for f in self.all_files if self.matches_type_filter(f)]
        else:
            self.filtered_files = [
                f for f in self.all_files 
                if search_text in f['name'].lower() and self.matches_type_filter(f)
            ]
        
        self.update_stats()
        self.display_assets()
    
    def matches_type_filter(self, file_info):
        """Check if file matches current type filter"""
        if self.filter_type == 'all':
            return True
        return file_info['category'] == self.filter_type
    
    def filter_by_type(self, type_name):
        """Filter assets by type"""
        type_map = {
            'All': 'all',
            'Images': 'image',
            'Videos': 'video',
            'Audio': 'audio',
            'Documents': 'document',
            'Other': 'other'
        }
        self.filter_type = type_map.get(type_name, 'all')
        self.filter_assets()
    
    def sort_assets(self, sort_by):
        """Sort assets"""
        sort_map = {
            'Name': 'name',
            'Size': 'size',
            'Date': 'mtime',
            'Type': 'ext'
        }
        self.sort_mode = sort_map.get(sort_by, 'name')
        
        reverse = self.sort_mode in ['size', 'mtime']
        self.filtered_files.sort(key=lambda f: f[self.sort_mode], reverse=reverse)
        self.display_assets()
    
    def change_view_mode(self, mode):
        """Switch between grid and list view"""
        self.view_mode = mode
        self.grid_btn.setChecked(mode == 'grid')
        self.list_btn.setChecked(mode == 'list')
        self.size_slider.setEnabled(mode == 'grid')
        self.display_assets()
    
    def change_thumbnail_size(self, size):
        """Change thumbnail size"""
        self.thumbnail_size = size
        if self.view_mode == 'grid':
            self.display_assets()
    
    def display_assets(self):
        """Display assets in current view mode"""
        # Clear existing widgets
        for _, _, widget in self.thumbnails:
            widget.deleteLater()
        self.thumbnails.clear()
        
        # Clear layout
        while self.grid_layout.count():
            item = self.grid_layout.takeAt(0)
            if item and item.widget():
                item.widget().deleteLater()
        
        if self.view_mode == 'grid':
            self.display_grid_view()
        else:
            self.display_list_view()
    
    def display_grid_view(self):
        """Display assets in grid view"""
        row = 0
        col = 0
        max_cols = max(1, int(600 / (self.thumbnail_size + 20)))
        
        for file_info in self.filtered_files:
            thumb_widget = self.create_thumbnail(file_info)
            self.grid_layout.addWidget(thumb_widget, row, col)
            self.thumbnails.append((file_info['name'], file_info['path'], thumb_widget))
            
            col += 1
            if col >= max_cols:
                col = 0
                row += 1
        
        # Add spacer
        self.grid_layout.setRowStretch(row + 1, 1)
    
    def display_list_view(self):
        """Display assets in list view"""
        for i, file_info in enumerate(self.filtered_files):
            list_widget = self.create_list_item(file_info)
            self.grid_layout.addWidget(list_widget, i, 0)
            self.thumbnails.append((file_info['name'], file_info['path'], list_widget))
        
        # Add spacer
        self.grid_layout.setRowStretch(len(self.filtered_files), 1)
    
    def create_thumbnail(self, file_info):
        """Create a thumbnail widget for an asset"""
        container = QFrame()
        container.setStyleSheet("""
            QFrame {
                background: #161b22;
                border: 2px solid #30363d;
                border-radius: 8px;
                padding: 8px;
            }
            QFrame:hover {
                border-color: #58a6ff;
                background: #21262d;
            }
        """)
        container.setCursor(Qt.CursorShape.PointingHandCursor)
        
        layout = QVBoxLayout(container)
        layout.setSpacing(8)
        
        # Subfolder badge (if not in root)
        if file_info['subfolder'] != 'Root':
            folder_badge = QLabel(f"📁 {file_info['subfolder']}")
            folder_badge.setStyleSheet("""
                QLabel {
                    background: #1f6feb;
                    color: white;
                    font-size: 9px;
                    padding: 2px 6px;
                    border-radius: 3px;
                    background: transparent;
                    border: none;
                }
            """)
            folder_badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
            folder_badge.setWordWrap(True)
            layout.addWidget(folder_badge)
        
        # Thumbnail image
        thumb_label = QLabel()
        thumb_label.setFixedSize(self.thumbnail_size, self.thumbnail_size)
        thumb_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        thumb_label.setStyleSheet("""
            QLabel {
                background: #0d1117;
                border: 1px solid #30363d;
                border-radius: 4px;
            }
        """)
        
        # Get icon based on category
        icon_map = {
            'image': '🖼️',
            'video': '🎬',
            'audio': '🎵',
            'document': '📄',
            'other': '📦'
        }
        icon = icon_map.get(file_info['category'], '📄')
        
        # Load and scale image (only for images)
        if file_info['category'] == 'image':
            try:
                pixmap = QPixmap(file_info['path'])
                if not pixmap.isNull():
                    scaled = pixmap.scaled(
                        self.thumbnail_size - 10, self.thumbnail_size - 10,
                        Qt.AspectRatioMode.KeepAspectRatio,
                        Qt.TransformationMode.SmoothTransformation
                    )
                    thumb_label.setPixmap(scaled)
                else:
                    thumb_label.setText(icon)
                    thumb_label.setStyleSheet(thumb_label.styleSheet() + f"font-size: {self.thumbnail_size//3}px;")
            except Exception:
                thumb_label.setText(icon)
                thumb_label.setStyleSheet(thumb_label.styleSheet() + f"font-size: {self.thumbnail_size//3}px;")
        else:
            thumb_label.setText(icon)
            thumb_label.setStyleSheet(thumb_label.styleSheet() + f"font-size: {self.thumbnail_size//3}px;")
        
        layout.addWidget(thumb_label)
        
        # Filename
        name_label = QLabel(file_info['name'])
        name_label.setWordWrap(True)
        name_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        name_label.setStyleSheet("""
            QLabel {
                color: #e6edf3;
                font-size: 11px;
                background: transparent;
                border: none;
            }
        """)
        layout.addWidget(name_label)
        
        # File size
        size_str = self.format_size(file_info['size'])
        size_label = QLabel(size_str)
        size_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        size_label.setStyleSheet("""
            QLabel {
                color: #8b949e;
                font-size: 10px;
                background: transparent;
                border: none;
            }
        """)
        layout.addWidget(size_label)
        
        # Make clickable
        container.mousePressEvent = lambda e: self.show_preview(file_info['name'], file_info['path'], file_info.get('rel_path', file_info['name']))
        
        return container
    
    def create_list_item(self, file_info):
        """Create a list item widget"""
        container = QFrame()
        container.setStyleSheet("""
            QFrame {
                background: #161b22;
                border: 1px solid #30363d;
                border-radius: 6px;
                padding: 8px;
            }
            QFrame:hover {
                border-color: #58a6ff;
                background: #21262d;
            }
        """)
        container.setCursor(Qt.CursorShape.PointingHandCursor)
        container.setMinimumHeight(60)
        
        layout = QHBoxLayout(container)
        layout.setSpacing(12)
        
        # Icon
        icon_map = {
            'image': '🖼️',
            'video': '🎬',
            'audio': '🎵',
            'document': '📄',
            'other': '📦'
        }
        icon_label = QLabel(icon_map.get(file_info['category'], '📄'))
        icon_label.setStyleSheet("font-size: 32px;")
        icon_label.setFixedSize(40, 40)
        icon_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(icon_label)
        
        # File info
        info_layout = QVBoxLayout()
        info_layout.setSpacing(4)
        
        # Display relative path if in subfolder
        display_name = file_info.get('rel_path', file_info['name'])
        if file_info['subfolder'] != 'Root':
            display_name = f"{file_info['subfolder']}/{file_info['name']}"
        else:
            display_name = file_info['name']
        
        name_label = QLabel(display_name)
        name_label.setStyleSheet("""
            color: #e6edf3;
            font-size: 13px;
            font-weight: 500;
        """)
        info_layout.addWidget(name_label)
        
        details = f"{file_info['ext'].upper()[1:]} • {self.format_size(file_info['size'])}"
        if file_info['subfolder'] != 'Root':
            details += f" • 📁 {file_info['subfolder']}"
        details_label = QLabel(details)
        details_label.setStyleSheet("""
            color: #8b949e;
            font-size: 11px;
        """)
        info_layout.addWidget(details_label)
        
        layout.addLayout(info_layout, 1)
        
        # Make clickable
        container.mousePressEvent = lambda e: self.show_preview(file_info['name'], file_info['path'], file_info.get('rel_path', file_info['name']))
        
        return container
    
    def format_size(self, size):
        """Format file size in human-readable format"""
        for unit in ['B', 'KB', 'MB', 'GB']:
            if size < 1024.0:
                return f"{size:.1f} {unit}"
            size /= 1024.0
        return f"{size:.1f} TB"
    
    def show_preview(self, filename, filepath, rel_path=None):
        """Show preview of selected asset"""
        self.current_preview = filepath
        
        try:
            # Get relative path for display
            if rel_path is None:
                rel_path = filename
            
            # Load full image
            pixmap = QPixmap(filepath)
            if not pixmap.isNull():
                # Scale to fit preview
                scaled = pixmap.scaled(
                    280, 400,
                    Qt.AspectRatioMode.KeepAspectRatio,
                    Qt.TransformationMode.SmoothTransformation
                )
                self.preview_label.setPixmap(scaled)
                
                # Update info
                size = os.path.getsize(filepath)
                width = pixmap.width()
                height = pixmap.height()
                
                info = f"""
<b>File:</b> {filename}<br>
<b>Path:</b> {rel_path}<br>
<b>Size:</b> {self.format_size(size)}<br>
<b>Dimensions:</b> {width} × {height}px<br>
<b>Format:</b> {os.path.splitext(filename)[1].upper()[1:]}
                """.strip()
                
                self.info_label.setText(info)
                self.open_btn.setEnabled(True)
                self.copy_path_btn.setEnabled(True)
                self.reveal_btn.setEnabled(True)
            else:
                self.preview_label.setText("⚠️ Cannot preview this file")
                info = f"""
<b>File:</b> {filename}<br>
<b>Path:</b> {rel_path}<br>
<b>Size:</b> {self.format_size(os.path.getsize(filepath))}<br>
<b>Type:</b> {os.path.splitext(filename)[1].upper()[1:]}
                """.strip()
                self.info_label.setText(info)
                self.open_btn.setEnabled(True)
                self.copy_path_btn.setEnabled(True)
                self.reveal_btn.setEnabled(True)
        except Exception as e:
            self.preview_label.setText(f"⚠️ Error: {str(e)}")
            self.info_label.setText("")
            self.open_btn.setEnabled(False)
            self.copy_path_btn.setEnabled(False)
            self.reveal_btn.setEnabled(False)
    
    def open_in_editor(self):
        """Open the current preview in the main editor"""
        if self.current_preview:
            main_window = self.window()
            if hasattr(main_window, 'open_file'):
                main_window.open_file(self.current_preview)
    
    def copy_path(self):
        """Copy file path to clipboard"""
        if self.current_preview:
            clipboard = QApplication.clipboard()
            if clipboard:
                clipboard.setText(self.current_preview)
                StatusManager.show_message("Copied to clipboard:", self.current_preview)
    
    def reveal_in_explorer(self):
        """Reveal file in system file explorer"""
        if self.current_preview and os.path.exists(self.current_preview):
            if sys.platform.startswith('win'):
                subprocess.run(['explorer', '/select,', self.current_preview])
            elif sys.platform.startswith('darwin'):
                subprocess.run(['open', '-R', self.current_preview])
            else:
                subprocess.run(['xdg-open', os.path.dirname(self.current_preview)])
    
    def close_tab(self):
        """Cleanup when tab is closed"""
        # Clear thumbnails
        for _, _, widget in self.thumbnails:
            widget.deleteLater()
        self.thumbnails.clear()
        
        # Clear preview
        self.preview_label.clear()
        self.current_preview = None
        
        self.deleteLater()
        gc.collect()

class MainWindow(QMainWindow):
    def show_sidebar_context_menu(self, position):
        from PyQt5.QtWidgets import QMenu
        index = self.tree.indexAt(position)
        menu = QMenu()
        menu.setStyleSheet("""
            QMenu {
                background: #161b22;
                color: #e6edf3;
                border: 1px solid #30363d;
                border-radius: 6px;
                padding: 6px;
            }
            QMenu::item {
                padding: 8px 24px;
                border-radius: 4px;
            }
            QMenu::item:selected {
                background: #1f6feb;
                color: #ffffff;
            }
            QMenu::separator {
                height: 1px;
                background: #30363d;
                margin: 6px 8px;
            }
        """)
        
        if index.isValid():
            file_path = self.model.filePath(index)
            
            if self.model.isDir(index):
                # Directory context menu
                create_file_action = QAction("New File", self)
                create_file_action.triggered.connect(lambda checked, path=file_path: self.create_file_dialog(path))
                menu.addAction(create_file_action)

                create_folder_action = QAction("New Folder", self)
                create_folder_action.triggered.connect(lambda checked, path=file_path: self.create_folder_dialog(path))
                menu.addAction(create_folder_action)
                
                menu.addSeparator()
                
                # Copy path action
                copy_path_action = QAction("Copy Path", self)
                copy_path_action.triggered.connect(lambda checked, path=file_path: self.copy_path_to_clipboard(path))
                menu.addAction(copy_path_action)
                
                # Reveal in explorer
                reveal_action = QAction("Reveal in Explorer", self)
                reveal_action.triggered.connect(lambda checked, path=file_path: self.reveal_in_explorer(path))
                menu.addAction(reveal_action)
                
                menu.addSeparator()
                
                rename_action = QAction("Rename", self)
                rename_action.triggered.connect(lambda checked, path=file_path: self.rename_file_dialog(path))
                menu.addAction(rename_action)
                
                delete_folder_action = QAction("Delete Folder", self)
                delete_folder_action.triggered.connect(lambda checked, path=file_path: self.delete_folder(path))
                menu.addAction(delete_folder_action)

            else:
                # File context menu
                open_action = QAction("Open", self)
                open_action.triggered.connect(lambda checked, path=file_path: self.open_file(path))
                menu.addAction(open_action)
                
                # Open with system default
                open_external_action = QAction("Open with System Default", self)
                open_external_action.triggered.connect(lambda checked, path=file_path: self.open_with_system_default(path))
                menu.addAction(open_external_action)
                
                menu.addSeparator()
                
                # Copy path action
                copy_path_action = QAction("Copy Path", self)
                copy_path_action.triggered.connect(lambda checked, path=file_path: self.copy_path_to_clipboard(path))
                menu.addAction(copy_path_action)
                
                # Copy relative path
                copy_rel_path_action = QAction("Copy Relative Path", self)
                copy_rel_path_action.triggered.connect(lambda checked, path=file_path: self.copy_relative_path_to_clipboard(path))
                menu.addAction(copy_rel_path_action)
                
                # Reveal in explorer
                reveal_action = QAction("Reveal in Explorer", self)
                reveal_action.triggered.connect(lambda checked, path=file_path: self.reveal_in_explorer(path))
                menu.addAction(reveal_action)
                
                menu.addSeparator()
                
                rename_action = QAction("Rename", self)
                rename_action.triggered.connect(lambda checked, path=file_path: self.rename_file_dialog(path))
                menu.addAction(rename_action)

                delete_action = QAction("Delete File", self)
                delete_action.triggered.connect(lambda checked, path=file_path: self.delete_file(path))
                menu.addAction(delete_action)
                
                menu.addSeparator()
                
                # File properties
                properties_action = QAction("Properties", self)
                properties_action.triggered.connect(lambda checked, path=file_path: self.show_file_properties(path))
                menu.addAction(properties_action)

        else:
            # Clicked on empty area: use root folder
            root_path = self.startup_folder if isinstance(self.startup_folder, str) and self.startup_folder else QDir.currentPath()

            create_file_action = QAction("New File", self)
            create_file_action.triggered.connect(lambda checked, path=root_path: self.create_file_dialog(path))
            menu.addAction(create_file_action)

            create_folder_action = QAction("New Folder", self)
            create_folder_action.triggered.connect(lambda checked, path=root_path: self.create_folder_dialog(path))
            menu.addAction(create_folder_action)
            
            menu.addSeparator()
            
            # Refresh action
            refresh_action = QAction("Refresh", self)
            refresh_action.triggered.connect(lambda: self.tree.setRootIndex(self.model.index(self.startup_folder)) if self.startup_folder else None)
            menu.addAction(refresh_action)

        viewport = self.tree.viewport()
        if viewport:
            menu.exec_(viewport.mapToGlobal(position))


    def delete_file(self, file_path):
        """Delete a file with confirmation"""
        if not isinstance(file_path, (str, bytes, os.PathLike)):
            print(f"Invalid file path (not a string/path): {file_path}")
            return
        
        if not os.path.exists(file_path):
            QMessageBox.warning(self, "Error", "File does not exist.")
            return
            
        # Ask for confirmation
        reply = QMessageBox.question(
            self, 
            "Delete File", 
            f"Are you sure you want to delete:\n{os.path.basename(file_path)}?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No
        )
        
        if reply == QMessageBox.StandardButton.Yes:
            try:
                os.remove(file_path)
                StatusManager.show_message("Deleted file:", file_path)
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to delete file:\n{e}")

    def delete_folder(self, folder_path):
        """Delete a folder with confirmation"""
        if not isinstance(folder_path, (str, bytes, os.PathLike)):
            print(f"Invalid folder path (not a string/path): {folder_path}")
            return
        
        if not os.path.exists(folder_path):
            QMessageBox.warning(self, "Error", "Folder does not exist.")
            return
        
        # Check if folder is empty
        if os.listdir(folder_path):
            reply = QMessageBox.question(
                self,
                "Delete Folder",
                f"Folder '{os.path.basename(folder_path)}' is not empty.\nDelete it and all its contents?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No
            )
        else:
            reply = QMessageBox.question(
                self,
                "Delete Folder",
                f"Are you sure you want to delete folder:\n{os.path.basename(folder_path)}?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No
            )
        
        if reply == QMessageBox.StandardButton.Yes:
            try:
                shutil.rmtree(folder_path)
                StatusManager.show_message("Deleted folder:", folder_path)
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to delete folder:\n{e}")

    def create_file_dialog(self, folder):
        """Create a new file in the specified folder"""
        name, ok = QInputDialog.getText(self, "New File", "Enter file name:")
        if ok and name:
            file_path = os.path.join(folder, name)
            if os.path.exists(file_path):
                QMessageBox.warning(self, "Error", f"File '{name}' already exists.")
                return
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write("")
                StatusManager.show_message("Created file:", file_path)
                # Optionally open the file
                self.open_file(file_path)
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to create file:\n{e}")

    def rename_file_dialog(self, file_path):
        """Rename a file or folder"""
        from PyQt5.QtWidgets import QInputDialog
        base = os.path.basename(file_path)
        folder = os.path.dirname(file_path)
        name, ok = QInputDialog.getText(self, "Rename", "Enter new name:", text=base)
        if ok and name and name != base:
            new_path = os.path.join(folder, name)
            if os.path.exists(new_path):
                QMessageBox.warning(self, "Error", f"'{name}' already exists.")
                return
            try:
                os.rename(file_path, new_path)
                StatusManager.show_message("Renamed:", f"{base} → {name}")
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Rename failed:\n{e}")

    def create_folder_dialog(self, parent_path):
        """Create a new folder in the specified directory"""
        folder_name, ok = QInputDialog.getText(self, "New Folder", "Enter folder name:")
        if ok and folder_name:
            new_folder_path = os.path.join(parent_path, folder_name)
            if os.path.exists(new_folder_path):
                QMessageBox.warning(self, "Error", f"Folder '{folder_name}' already exists.")
                return
            try:
                os.makedirs(new_folder_path)
                StatusManager.show_message("Created folder:", new_folder_path)
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to create folder:\n{e}")
    
    def copy_path_to_clipboard(self, file_path):
        """Copy full file path to clipboard"""
        clipboard = QApplication.clipboard()
        if clipboard:
            clipboard.setText(file_path)
            StatusManager.show_message("Copied to clipboard:", file_path)
    
    def copy_relative_path_to_clipboard(self, file_path):
        """Copy relative file path to clipboard"""
        if self.startup_folder:
            rel_path = os.path.relpath(file_path, self.startup_folder)
            clipboard = QApplication.clipboard()
            if clipboard:
                clipboard.setText(rel_path)
                StatusManager.show_message("Copied relative path:", rel_path)
        else:
            self.copy_path_to_clipboard(file_path)
    
    def reveal_in_explorer(self, file_path):
        """Reveal file or folder in system file explorer"""
        if not os.path.exists(file_path):
            QMessageBox.warning(self, "Error", "Path does not exist.")
            return
        
        try:
            if sys.platform.startswith('win'):
                # Windows: select the file/folder
                subprocess.run(['explorer', '/select,', os.path.normpath(file_path)])
            elif sys.platform.startswith('darwin'):
                # macOS: reveal in Finder
                subprocess.run(['open', '-R', file_path])
            else:
                # Linux: open containing folder
                folder = file_path if os.path.isdir(file_path) else os.path.dirname(file_path)
                subprocess.run(['xdg-open', folder])
            StatusManager.show_message("Revealed in explorer:", file_path)
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to reveal in explorer:\n{e}")
    
    def open_with_system_default(self, file_path):
        """Open file with system default application"""
        if not os.path.exists(file_path):
            QMessageBox.warning(self, "Error", "File does not exist.")
            return
        
        try:
            if sys.platform.startswith('win'):
                os.startfile(file_path)
            elif sys.platform.startswith('darwin'):
                subprocess.run(['open', file_path])
            else:
                subprocess.run(['xdg-open', file_path])
            StatusManager.show_message("Opened with system default:", file_path)
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to open file:\n{e}")
    
    def show_file_properties(self, file_path):
        """Show file properties dialog"""
        if not os.path.exists(file_path):
            QMessageBox.warning(self, "Error", "File does not exist.")
            return
        
        # Get file info
        stat_info = os.stat(file_path)
        file_size = stat_info.st_size
        modified_time = datetime.fromtimestamp(stat_info.st_mtime)
        created_time = datetime.fromtimestamp(stat_info.st_ctime)
        
        # Format size
        size_str = self.format_file_size(file_size)
        
        # Get file extension and type
        file_name = os.path.basename(file_path)
        file_ext = os.path.splitext(file_name)[1] or "No extension"
        
        # Create dialog
        dialog = QDialog(self)
        dialog.setWindowTitle(f"Properties - {file_name}")
        dialog.setMinimumWidth(400)
        
        layout = QVBoxLayout(dialog)
        
        # Info text
        info_html = f"""
        <style>
            table {{ color: #e6edf3; font-size: 13px; }}
            td {{ padding: 8px; }}
            .label {{ color: #8b949e; font-weight: bold; }}
        </style>
        <table>
            <tr><td class='label'>Name:</td><td>{file_name}</td></tr>
            <tr><td class='label'>Path:</td><td>{file_path}</td></tr>
            <tr><td class='label'>Type:</td><td>{file_ext}</td></tr>
            <tr><td class='label'>Size:</td><td>{size_str} ({file_size:,} bytes)</td></tr>
            <tr><td class='label'>Modified:</td><td>{modified_time.strftime('%Y-%m-%d %H:%M:%S')}</td></tr>
            <tr><td class='label'>Created:</td><td>{created_time.strftime('%Y-%m-%d %H:%M:%S')}</td></tr>
        </table>
        """
        
        info_label = QLabel(info_html)
        info_label.setWordWrap(True)
        info_label.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        layout.addWidget(info_label)
        
        # Close button
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(dialog.close)
        layout.addWidget(close_btn)
        
        dialog.exec_()
    
    def format_file_size(self, size):
        """Format file size in human-readable format"""
        for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
            if size < 1024.0:
                return f"{size:.1f} {unit}"
            size /= 1024.0
        return f"{size:.1f} PB"

    def _shorten_filename(self, filename, max_length=13):
        """Shorten filename to max_length characters"""
        if len(filename) <= max_length:
            return filename
        
        # Show first 10 characters + ...
        return filename[:10] + "..."
    
    def update_tab_title_modified(self, tab):
        for i in range(self.tabs.count()):
            t = self.tabs.widget(i)
            if t is tab and hasattr(t, 'file_path'):
                base_name = t.file_path.split("/")[-1] if t.file_path and "/" in t.file_path else (t.file_path.split("\\")[-1] if t.file_path else "Untitled")
                # Shorten the filename if needed
                short_name = self._shorten_filename(base_name, max_length=13)
                modified = "*" if hasattr(t, "is_modified") and callable(t.is_modified) and t.is_modified() else ""
                self.tabs.setTabText(i, short_name + modified)
                
                # Visual indicator for unsaved changes
                if modified:
                    # Set a subtle background color for modified tabs
                    tab_bar = self.tabs.tabBar()
                    if tab_bar:
                        tab_bar.setTabTextColor(i, QColor("#f0883e"))  # Orange color for modified
                else:
                    tab_bar = self.tabs.tabBar()
                    if tab_bar:
                        tab_bar.setTabTextColor(i, QColor("#e6edf3"))  # Default color
                break
    font_family = "Consolas"
    font_size = 12
    tab_size = 4
    dark_mode = True
    line_spacing = 1
    theme = "Dark"
    preview_layout = "Horizontal Split"
    settings_path = settings_path

    def load_settings(self):
        self.startup_folder = None
        if os.path.exists(self.settings_path):
            try:
                with open(self.settings_path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                self.font_family = data.get("font_family", self.font_family)
                self.font_size = data.get("font_size", self.font_size)
                self.tab_size = data.get("tab_size", self.tab_size)
                self.dark_mode = data.get("dark_mode", self.dark_mode)
                self.line_spacing = data.get("line_spacing", self.line_spacing)
                self.theme = data.get("theme", self.theme)
                self.preview_layout = data.get("preview_layout", self.preview_layout)
                self.startup_folder = data.get("startup_folder", None)
            except Exception:
                pass

    def save_settings(self):
        data = {
            "font_family": self.font_family,
            "font_size": self.font_size,
            "tab_size": self.tab_size,
            "dark_mode": self.dark_mode,
            "line_spacing": self.line_spacing,
            "theme": self.theme,
            "preview_layout": self.preview_layout,
            "startup_folder": self.startup_folder,
        }
        try:
            with open(self.settings_path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
        except Exception:
            pass
    def open_settings(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("Settings")
        layout = QFormLayout(dialog)

        font_combo = QComboBox()
        font_combo.addItems(["Consolas", "Courier New", "JetBrains Mono"])
        font_combo.setCurrentText(self.font_family)
        layout.addRow("Font:", font_combo)

        font_size_spin = QSpinBox()
        font_size_spin.setRange(6, 32)
        font_size_spin.setValue(self.font_size)
        layout.addRow("Font Size:", font_size_spin)

        tab_size_spin = QSpinBox()
        tab_size_spin.setRange(2, 8)
        tab_size_spin.setValue(self.tab_size)
        layout.addRow("Tab Size:", tab_size_spin)

        line_spacing_spin = QSpinBox()
        line_spacing_spin.setRange(1, 8)
        line_spacing_spin.setValue(getattr(self, "line_spacing", 1))
        layout.addRow("Line Spacing:", line_spacing_spin)

        theme_combo = QComboBox()
        theme_combo.addItems(["Dark"])
        theme_combo.setCurrentText(getattr(self, "theme", "Dark"))
        layout.addRow("Theme:", theme_combo)

        preview_layout_combo = QComboBox()
        preview_layout_combo.addItems(["Horizontal Split", "Vertical Split"])
        preview_layout_combo.setCurrentText(getattr(self, "preview_layout", "Horizontal Split"))
        layout.addRow("Preview Layout:", preview_layout_combo)

        dark_mode_check = QCheckBox("Enable Dark Mode")
        dark_mode_check.setChecked(self.dark_mode)

        apply_btn = QPushButton("Apply")
        layout.addRow(apply_btn)

        def apply_settings():
            self.font_family = font_combo.currentText()
            self.font_size = font_size_spin.value()
            self.tab_size = tab_size_spin.value()
            self.dark_mode = dark_mode_check.isChecked()
            self.line_spacing = line_spacing_spin.value()
            self.theme = theme_combo.currentText()
            self.preview_layout = preview_layout_combo.currentText()
            self.apply_theme(self.theme)
            # Line spacing
            spacing = self.line_spacing
            for i in range(self.tabs.count()):
                tab = self.tabs.widget(i)
                if tab and hasattr(tab, 'editor') and tab.editor:
                    font = tab.editor.font()
                    tab.editor.setFont(font)
                    tab.editor.setStyleSheet(f"line-height: {spacing};")
            # Preview layout (for MarkdownTab)
            layout_mode = self.preview_layout
            for i in range(self.tabs.count()):
                tab = self.tabs.widget(i)
                if tab and isinstance(tab, MarkdownTab):
                    tab.set_layout_mode(layout_mode)
            self.apply_settings_to_editors()
            self.save_settings()
            dialog.accept()

        apply_btn.clicked.connect(apply_settings)
        dialog.exec_()

    def apply_settings_to_editors(self):
        for i in range(self.tabs.count()):
            tab = self.tabs.widget(i)
            if tab and hasattr(tab, 'editor') and tab.editor:
                try:
                    metrics = tab.editor.fontMetrics()
                    tab.editor.setFont(QFont(self.font_family, self.font_size))
                    if metrics:
                        tab.editor.setTabStopDistance(self.tab_size * metrics.width(' '))
                except RuntimeError:
                    # Editor has been deleted; skip this tab
                    continue

    def apply_theme(self, theme_name="Dark"):
        themes = {
            "Dark": """
                /* Main Window - Modern Dark Theme */
                QMainWindow { 
                    background-color: #0d1117; 
                }
                QWidget { 
                    background-color: #161b22; 
                    color: #e6edf3; 
                    font-family: 'Segoe UI', 'SF Pro Display', -apple-system, BlinkMacSystemFont, sans-serif;
                    font-size: 13px;
                }
                
                /* Editor - Enhanced */
                QPlainTextEdit, QTextEdit { 
                    background-color: #0d1117; 
                    color: #e6edf3; 
                    border: none;
                    selection-background-color: #1f6feb;
                    selection-color: #ffffff;
                    padding: 8px;
                    font-family: 'JetBrains Mono', 'Fira Code', 'Consolas', monospace;
                    line-height: 1.6;
                }
                
                /* Tabs - Modern Style */
                QTabWidget::pane { 
                    border: none; 
                    background: #0d1117;
                    border-top: 1px solid #30363d;
                }
                QTabBar { 
                    qproperty-drawBase: 0;
                }
                QTabBar::tab {
                    background: #161b22; 
                    color: #8b949e; 
                    border: none;
                    padding: 10px 18px 10px 14px;      /* more space on right for close button */
                    border-top-left-radius: 6px;
                    border-top-right-radius: 6px;
                    font-weight: 500;
                    max-width: 120px;
                }
                

                QTabBar::tab:selected { 
                    background: #0d1117; 
                    color: #e6edf3;
                    border-bottom: 2px solid #1f6feb;
                }
                QTabBar::tab:hover:!selected { 
                    background: #21262d; 
                    color: #c9d1d9;
                }
                
                /* Tree View - Enhanced */
                QTreeView { 
                    background-color: #161b22; 
                    color: #e6edf3; 
                    border: none;
                    border-right: 1px solid #21262d;
                    outline: none;
                    font-size: 13px;
                    padding: 8px 4px;
                }
                QTreeView::item { 
                    padding: 6px 12px;
                    border-radius: 6px;
                    margin: 2px 4px;
                }
                QTreeView::item:hover { 
                    background-color: #21262d;
                }
                QTreeView::item:selected { 
                    background-color: #1f6feb; 
                    color: #ffffff;
                }
                
                /* Menu Bar - Modern */
                QMenuBar { 
                    background: #161b22; 
                    color: #e6edf3;
                    border-bottom: 1px solid #21262d;
                    padding: 4px;
                    spacing: 4px;
                }
                QMenuBar::item { 
                    padding: 8px 16px;
                    background: transparent;
                    border-radius: 6px;
                    margin: 2px;
                }
                QMenuBar::item:selected { 
                    background: #21262d;
                    color: #58a6ff;
                }
                
                /* Menu - Enhanced */
                QMenu { 
                    background: #161b22; 
                    color: #e6edf3;
                    border: 1px solid #30363d;
                    border-radius: 8px;
                    padding: 8px;
                }
                QMenu::item { 
                    padding: 8px 32px 8px 16px;
                    border-radius: 6px;
                    margin: 2px 4px;
                }
                QMenu::item:selected { 
                    background: #1f6feb;
                    color: #ffffff;
                }
                QMenu::separator {
                    height: 1px;
                    background: #30363d;
                    margin: 6px 12px;
                }
                
                /* Buttons - Modern Style */
                QPushButton { 
                    background: #1f6feb; 
                    color: #ffffff; 
                    border: 1px solid #1f6feb;
                    padding: 8px 20px;
                    border-radius: 6px;
                    font-weight: 500;
                    font-size: 13px;
                }
                QPushButton:hover { 
                    background: #388bfd;
                    border-color: #58a6ff;
                }
                QPushButton:pressed { 
                    background: #1a5ecc;
                    transform: scale(0.98);
                }
                QPushButton:disabled {
                    background: #21262d;
                    color: #6e7681;
                    border-color: #30363d;
                }
                
                /* Input Fields - Enhanced */
                QLineEdit, QComboBox, QSpinBox { 
                    background: #0d1117; 
                    color: #e6edf3;
                    border: 1px solid #30363d;
                    padding: 8px 12px;
                    border-radius: 6px;
                    selection-background-color: #1f6feb;
                }
                QLineEdit:focus, QComboBox:focus, QSpinBox:focus {
                    border: 1px solid #1f6feb;
                    background: #0d1117;
                }
                QComboBox::drop-down {
                    border: none;
                    width: 20px;
                }
                QComboBox::down-arrow {
                    image: url(none);
                    border-left: 5px solid transparent;
                    border-right: 5px solid transparent;
                    border-top: 6px solid #8b949e;
                    margin-right: 8px;
                }
                QComboBox QAbstractItemView {
                    background: #161b22;
                    color: #e6edf3;
                    border: 1px solid #30363d;
                    border-radius: 6px;
                    selection-background-color: #1f6feb;
                    padding: 4px;
                }
                
                /* Scrollbar - Modern Custom Style */
                /* Vertical Scrollbar */
                QScrollBar:vertical {
                    background: #0d1117;
                    width: 14px;
                    border: none;
                }
                QScrollBar::handle:vertical {
                    background: #30363d;
                    min-height: 40px;
                    border-radius: 7px;
                    margin: 3px 2px;
                    border: none;
                }
                QScrollBar::handle:vertical:hover {
                    background: #484f58;
                }
                QScrollBar::handle:vertical:pressed {
                    background: #58a6ff;
                }
                QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
                    height: 0px;
                    border: none;
                    background: none;
                }
                QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {
                    background: none;
                }
                
                /* Horizontal Scrollbar */
                QScrollBar:horizontal {
                    background: #0d1117;
                    height: 14px;
                    border: none;
                }
                QScrollBar::handle:horizontal {
                    background: #30363d;
                    min-width: 40px;
                    border-radius: 7px;
                    margin: 2px 3px;
                    border: none;
                }
                QScrollBar::handle:horizontal:hover {
                    background: #484f58;
                }
                QScrollBar::handle:horizontal:pressed {
                    background: #58a6ff;
                }
                QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {
                    width: 0px;
                    border: none;
                    background: none;
                }
                QScrollBar::add-page:horizontal, QScrollBar::sub-page:horizontal {
                    background: none;
                }
                
                /* Splitter - Subtle */
                QSplitter::handle {
                    background: #21262d;
                    width: 2px;
                }
                QSplitter::handle:hover {
                    background: #1f6feb;
                }
                
                /* Status Bar - Modern */
                QStatusBar {
                    background: #1f6feb;
                    color: #ffffff;
                    border-top: none;
                    padding: 6px 12px;
                    font-weight: 500;
                }
                
                /* Checkbox - Modern */
                QCheckBox {
                    color: #e6edf3;
                    spacing: 10px;
                }
                QCheckBox::indicator {
                    width: 18px;
                    height: 18px;
                    border: 2px solid #30363d;
                    border-radius: 4px;
                    background: #0d1117;
                }
                QCheckBox::indicator:hover {
                    border-color: #58a6ff;
                }
                QCheckBox::indicator:checked {
                    background: #1f6feb;
                    border-color: #1f6feb;
                    image: url(none);
                }
                
                /* Tooltips - Modern */
                QToolTip { 
                    background: #161b22; 
                    color: #e6edf3; 
                    border: 1px solid #30363d;
                    border-radius: 6px;
                    padding: 6px 10px;
                }
                
                /* Dialog - Enhanced */
                QDialog {
                    background: #0d1117;
                    border-radius: 12px;
                }
                QLabel {
                    color: #e6edf3;
                }
                
                /* Form Layout */
                QFormLayout {
                    spacing: 12px;
                }

                /* QTreeView White Expand/Collapse Arrows (Pure CSS) */
QTreeView::indicator {
    width: 14px;
    height: 14px;
    padding: 2px;
    background: transparent;
}

/* Closed ► */
QTreeView::indicator:closed {
    border-left: 6px solid #ffffff;
    border-top: 4px solid transparent;
    border-bottom: 4px solid transparent;
}

/* Open ▼ */
QTreeView::indicator:open {
    border-top: 6px solid #ffffff;
    border-left: 4px solid transparent;
    border-right: 4px solid transparent;
}

/* Hover Highlight */
QTreeView::indicator:hover {
    border-left-color: #58a6ff;
    border-top-color: #58a6ff;
}

            """,
        }
        stylesheet = themes.get(theme_name, themes["Dark"])
        parent = self.parent()
        if parent:
            parent.setStyleSheet(stylesheet)
        else:
            self.setStyleSheet(stylesheet)
    def setup_shortcuts(self):
        # F5: reload folder
        reload_folder_action = QAction("Reload Folder", self)
        reload_folder_action.setShortcut("F5")
        reload_folder_action.triggered.connect(lambda: self.tree.setRootIndex(self.model.index(self.startup_folder)) if self.startup_folder else None)
        menubar = self.menuBar()
        if menubar:
            menubar.addAction(reload_folder_action)

        # Ctrl+Tab: next tab
        next_tab_action = QAction("Next Tab", self)
        next_tab_action.setShortcut("Ctrl+Tab")
        next_tab_action.triggered.connect(self.next_tab)
        self.addAction(next_tab_action)

        # Ctrl+Shift+Tab: previous tab
        prev_tab_action = QAction("Previous Tab", self)
        prev_tab_action.setShortcut("Ctrl+Shift+Tab")
        prev_tab_action.triggered.connect(self.prev_tab)
        self.addAction(prev_tab_action)

        # Ctrl+Q: quit
        quit_action = QAction("Quit", self)
        quit_action.setShortcut("Ctrl+Q")
        quit_action.triggered.connect(self.close)
        self.menuBar().addAction(quit_action)

        # Ctrl+L: quick open
        quick_open_action = QAction("Quick Open", self)
        quick_open_action.setShortcut("Ctrl+L")
        quick_open_action.triggered.connect(self.show_quick_open)
        self.addAction(quick_open_action)
        
        # Ctrl+Shift+F: Find in files (global search)
        find_in_files_action = QAction("Find in Files", self)
        find_in_files_action.setShortcut("Ctrl+Shift+F")
        find_in_files_action.triggered.connect(self.show_find_in_files)
        self.addAction(find_in_files_action)
        
        # Ctrl+P: Command Palette
        command_palette_action = QAction("Command Palette", self)
        command_palette_action.setShortcut("Ctrl+P")
        command_palette_action.triggered.connect(self.show_command_palette)
        self.addAction(command_palette_action)
        
        # F11: Toggle fullscreen
        fullscreen_action = QAction("Toggle Fullscreen", self)
        fullscreen_action.setShortcut("F11")
        fullscreen_action.triggered.connect(self.toggle_fullscreen)
        self.addAction(fullscreen_action)
        
        # Ctrl+G: Go to Line
        goto_line_action = QAction("Go to Line", self)
        goto_line_action.setShortcut("Ctrl+G")
        goto_line_action.triggered.connect(self.show_goto_line)
        self.addAction(goto_line_action)
        
        # Ctrl+F: Find in current file
        find_action = QAction("Find", self)
        find_action.setShortcut("Ctrl+F")
        find_action.triggered.connect(self.show_find)
        self.addAction(find_action)

    def next_tab(self):
        idx = self.tabs.currentIndex()
        if self.tabs.count() > 1:
            self.tabs.setCurrentIndex((idx + 1) % self.tabs.count())

    def prev_tab(self):
        idx = self.tabs.currentIndex()
        if self.tabs.count() > 1:
            self.tabs.setCurrentIndex((idx - 1) % self.tabs.count())
    
    def toggle_fullscreen(self):
        """Toggle fullscreen mode"""
        if self.isFullScreen():
            self.showNormal()
            StatusManager.show_message("Exited fullscreen mode")
        else:
            self.showFullScreen()
            StatusManager.show_message("Entered fullscreen mode (F11 to exit)")
    
    def show_command_palette(self):
        """Show command palette for quick actions"""
        from PyQt5.QtWidgets import QListWidget, QListWidgetItem
        
        dialog = QDialog(self)
        dialog.setWindowTitle("Command Palette")
        dialog.setMinimumWidth(600)
        dialog.setMinimumHeight(400)
        
        layout = QVBoxLayout(dialog)
        
        # Search box
        search_box = QLineEdit()
        search_box.setPlaceholderText("Type a command...")
        search_box.setStyleSheet("""
            QLineEdit {
                font-size: 16px;
                padding: 12px;
                border: 2px solid #1f6feb;
                border-radius: 8px;
            }
        """)
        layout.addWidget(search_box)
        
        # Command list
        command_list = QListWidget()
        command_list.setStyleSheet("""
            QListWidget {
                background-color: #0d1117;
                color: #e6edf3;
                border: 1px solid #30363d;
                border-radius: 6px;
                padding: 4px;
                font-size: 14px;
            }
            QListWidget::item {
                padding: 12px;
                border-radius: 4px;
            }
            QListWidget::item:selected {
                background-color: #1f6feb;
                color: #ffffff;
            }
            QListWidget::item:hover:!selected {
                background-color: #21262d;
            }
        """)
        layout.addWidget(command_list)
        
        # Define commands
        commands = [
            ("📂 Open Folder", self.open_folder),
            ("📄 Open File", self.open_file_dialog),
            ("➕ New File", self.new_file),
            ("💾 Save", self.save_file),
            ("💾 Save As", self.save_file_as),
            ("🔍 Quick Open (Ctrl+L)", self.show_quick_open),
            ("🔎 Find in Files (Ctrl+Shift+F)", self.show_find_in_files),
            ("🔍 Find in Current File (Ctrl+F)", self.show_find),
            ("🔢 Go to Line (Ctrl+G)", self.show_goto_line),
            ("⚙️ Settings", self.open_settings),
            ("🖥️ Toggle Fullscreen (F11)", self.toggle_fullscreen),
            ("❌ Close Tab (Ctrl+W)", lambda: self.close_tab(self.tabs.currentIndex())),
            ("🔄 Reload Folder (F5)", lambda: self.tree.setRootIndex(self.model.index(self.startup_folder)) if self.startup_folder else None),
            ("➡️ Next Tab (Ctrl+Tab)", self.next_tab),
            ("⬅️ Previous Tab (Ctrl+Shift+Tab)", self.prev_tab),
        ]
        
        # Populate list
        def update_list(filter_text=""):
            command_list.clear()
            filter_lower = filter_text.lower()
            for name, action in commands:
                if not filter_text or filter_lower in name.lower():
                    item = QListWidgetItem(name)
                    item.setData(Qt.ItemDataRole.UserRole, action)
                    command_list.addItem(item)
            if command_list.count() > 0:
                command_list.setCurrentRow(0)
        
        update_list()
        
        # Connect signals
        search_box.textChanged.connect(update_list)
        
        def execute_command():
            current_item = command_list.currentItem()
            if current_item:
                action = current_item.data(Qt.ItemDataRole.UserRole)
                dialog.accept()
                action()
        
        command_list.itemDoubleClicked.connect(lambda: execute_command())
        
        # Handle Enter key
        def handle_key_press(e):
            if e and e.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                execute_command()
            else:
                QListWidget.keyPressEvent(command_list, e)
        
        command_list.keyPressEvent = handle_key_press
        
        # Focus search box
        search_box.setFocus()
        
        dialog.exec_()
    
    def show_find_in_files(self):
        """Show find in files dialog for global search"""
        if not self.startup_folder:
            QMessageBox.information(self, "Find in Files", "Please open a folder first (Ctrl+O)")
            return
        
        from PyQt5.QtWidgets import QListWidget, QListWidgetItem, QTextBrowser
        
        dialog = QDialog(self)
        dialog.setWindowTitle("Find in Files")
        dialog.setMinimumWidth(800)
        dialog.setMinimumHeight(600)
        
        layout = QVBoxLayout(dialog)
        
        # Search options
        search_layout = QHBoxLayout()
        search_box = QLineEdit()
        search_box.setPlaceholderText("Enter search term...")
        search_box.setStyleSheet("""
            QLineEdit {
                font-size: 14px;
                padding: 10px;
                border: 2px solid #30363d;
                border-radius: 6px;
            }
            QLineEdit:focus {
                border-color: #1f6feb;
            }
        """)
        search_layout.addWidget(search_box, 1)
        
        case_sensitive_check = QCheckBox("Case Sensitive")
        case_sensitive_check.setStyleSheet("color: #e6edf3;")
        search_layout.addWidget(case_sensitive_check)
        
        search_btn = QPushButton("🔍 Search")
        search_btn.setStyleSheet("""
            QPushButton {
                padding: 10px 20px;
                font-size: 14px;
                font-weight: bold;
            }
        """)
        search_layout.addWidget(search_btn)
        
        layout.addLayout(search_layout)
        
        # Results area
        results_label = QLabel("Results will appear here")
        results_label.setStyleSheet("color: #8b949e; padding: 8px;")
        layout.addWidget(results_label)
        
        # Results list
        results_list = QListWidget()
        results_list.setStyleSheet("""
            QListWidget {
                background-color: #0d1117;
                color: #e6edf3;
                border: 1px solid #30363d;
                border-radius: 6px;
                padding: 4px;
                font-family: 'Consolas', monospace;
                font-size: 12px;
            }
            QListWidget::item {
                padding: 8px;
                border-radius: 4px;
                border-left: 3px solid transparent;
            }
            QListWidget::item:selected {
                background-color: #1f6feb;
                color: #ffffff;
                border-left-color: #58a6ff;
            }
            QListWidget::item:hover:!selected {
                background-color: #21262d;
            }
        """)
        layout.addWidget(results_list)
        
        # Progress bar
        progress = QProgressBar()
        progress.setStyleSheet("""
            QProgressBar {
                border: 1px solid #30363d;
                border-radius: 4px;
                text-align: center;
                background: #0d1117;
                color: #e6edf3;
            }
            QProgressBar::chunk {
                background-color: #1f6feb;
                border-radius: 3px;
            }
        """)
        progress.setVisible(False)
        layout.addWidget(progress)
        
        # Close button
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(dialog.close)
        layout.addWidget(close_btn)
        
        # Search function
        def perform_search():
            search_term = search_box.text().strip()
            if not search_term:
                return
            
            results_list.clear()
            results_label.setText("Searching...")
            progress.setVisible(True)
            progress.setRange(0, 0)  # Indeterminate
            
            QApplication.processEvents()
            
            results = []
            file_count = 0
            
            try:
                # Walk through all files
                for root, dirs, files in os.walk(self.startup_folder):
                    # Skip hidden directories
                    dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['__pycache__', 'node_modules', 'venv', 'env']]
                    
                    for file in files:
                        if file.startswith('.'):
                            continue
                        
                        # Only search in text files
                        if not file.endswith(('.txt', '.md', '.py', '.js', '.html', '.css', '.json', '.xml', '.csv', '.log')):
                            continue
                        
                        file_count += 1
                        full_path = os.path.join(root, file)
                        
                        try:
                            with open(full_path, 'r', encoding='utf-8', errors='ignore') as f:
                                for line_num, line in enumerate(f, 1):
                                    # Search with case sensitivity option
                                    if case_sensitive_check.isChecked():
                                        if search_term in line:
                                            rel_path = os.path.relpath(full_path, self.startup_folder)
                                            results.append((rel_path, line_num, line.strip(), full_path))
                                    else:
                                        if search_term.lower() in line.lower():
                                            rel_path = os.path.relpath(full_path, self.startup_folder)
                                            results.append((rel_path, line_num, line.strip(), full_path))
                        except Exception:
                            continue
            except Exception as e:
                results_label.setText(f"Error during search: {e}")
                progress.setVisible(False)
                return
            
            # Display results
            progress.setVisible(False)
            results_list.clear()
            
            if results:
                results_label.setText(f"Found {len(results)} matches in {file_count} files")
                
                for rel_path, line_num, line_text, full_path in results:
                    # Highlight search term in results
                    if case_sensitive_check.isChecked():
                        display_text = line_text.replace(search_term, f"**{search_term}**")
                    else:
                        # Case insensitive highlighting
                        import re
                        pattern = re.compile(re.escape(search_term), re.IGNORECASE)
                        display_text = pattern.sub(lambda m: f"**{m.group()}**", line_text)
                    
                    item_text = f"📄 {rel_path}:{line_num}\n    {display_text[:100]}"
                    item = QListWidgetItem(item_text)
                    item.setData(Qt.ItemDataRole.UserRole, (full_path, line_num))
                    results_list.addItem(item)
            else:
                results_label.setText(f"No matches found (searched {file_count} files)")
        
        # Open file on double click
        def open_result():
            current_item = results_list.currentItem()
            if current_item:
                file_path, line_num = current_item.data(Qt.ItemDataRole.UserRole)
                self.open_file(file_path)
                # TODO: Jump to line number (would need to add method to EditorTab)
                dialog.close()
        
        search_btn.clicked.connect(perform_search)
        results_list.itemDoubleClicked.connect(open_result)
        search_box.returnPressed.connect(perform_search)
        
        # Focus search box
        search_box.setFocus()
        
        dialog.exec_()
    
    def show_goto_line(self):
        """Show Go to Line dialog"""
        current_tab = self.tabs.currentWidget()
        if not current_tab or not hasattr(current_tab, 'editor'):
            QMessageBox.information(self, "Go to Line", "No text editor is currently active")
            return
        
        editor = current_tab.editor
        total_lines = editor.blockCount()
        
        line_num, ok = QInputDialog.getInt(
            self, 
            "Go to Line", 
            f"Enter line number (1-{total_lines}):",
            1, 1, total_lines
        )
        
        if ok:
            # Move cursor to the line
            cursor = editor.textCursor()
            cursor.movePosition(cursor.MoveOperation.Start)
            cursor.movePosition(cursor.MoveOperation.Down, cursor.MoveMode.MoveAnchor, line_num - 1)
            editor.setTextCursor(cursor)
            editor.centerCursor()
            editor.setFocus()
            StatusManager.show_message(f"Jumped to line {line_num}")
    
    def show_find(self):
        """Show find dialog for current editor"""
        current_tab = self.tabs.currentWidget()
        if not current_tab or not hasattr(current_tab, 'editor'):
            QMessageBox.information(self, "Find", "No text editor is currently active")
            return
        
        editor = current_tab.editor
        
        # Create find dialog
        dialog = QDialog(self)
        dialog.setWindowTitle("Find")
        dialog.setMinimumWidth(400)
        
        layout = QVBoxLayout(dialog)
        
        # Search input
        search_layout = QHBoxLayout()
        search_label = QLabel("Find:")
        search_layout.addWidget(search_label)
        
        search_box = QLineEdit()
        search_box.setPlaceholderText("Enter text to find...")
        search_box.setStyleSheet("""
            QLineEdit {
                padding: 8px;
                font-size: 13px;
                border: 1px solid #30363d;
                border-radius: 4px;
            }
            QLineEdit:focus {
                border-color: #1f6feb;
            }
        """)
        search_layout.addWidget(search_box)
        layout.addLayout(search_layout)
        
        # Options
        options_layout = QHBoxLayout()
        case_check = QCheckBox("Match Case")
        whole_word_check = QCheckBox("Whole Word")
        options_layout.addWidget(case_check)
        options_layout.addWidget(whole_word_check)
        options_layout.addStretch()
        layout.addLayout(options_layout)
        
        # Buttons
        button_layout = QHBoxLayout()
        find_next_btn = QPushButton("Find Next")
        find_prev_btn = QPushButton("Find Previous")
        replace_btn = QPushButton("Replace")
        replace_all_btn = QPushButton("Replace All")
        close_btn = QPushButton("Close")
        
        button_layout.addWidget(find_next_btn)
        button_layout.addWidget(find_prev_btn)
        button_layout.addWidget(replace_btn)
        button_layout.addWidget(replace_all_btn)
        button_layout.addStretch()
        button_layout.addWidget(close_btn)
        layout.addLayout(button_layout)
        
        # Replace input (initially hidden)
        replace_layout = QHBoxLayout()
        replace_label = QLabel("Replace:")
        replace_layout.addWidget(replace_label)
        
        replace_box = QLineEdit()
        replace_box.setPlaceholderText("Replace with...")
        replace_box.setStyleSheet(search_box.styleSheet())
        replace_layout.addWidget(replace_box)
        layout.insertLayout(1, replace_layout)
        
        # Results label
        results_label = QLabel("")
        results_label.setStyleSheet("color: #8b949e; padding: 4px;")
        layout.addWidget(results_label)
        
        # Find function
        def find_text(forward=True):
            search_text = search_box.text()
            if not search_text:
                return False
            
            # Build search flags
            from PyQt5.QtGui import QTextDocument
            flags = QTextDocument.FindFlag(0)
            
            if case_check.isChecked():
                flags |= QTextDocument.FindFlag.FindCaseSensitively
            if whole_word_check.isChecked():
                flags |= QTextDocument.FindFlag.FindWholeWords
            if not forward:
                flags |= QTextDocument.FindFlag.FindBackward
            
            # Perform search
            found = editor.find(search_text, flags)
            
            if found:
                results_label.setText("Match found")
                results_label.setStyleSheet("color: #238636; padding: 4px;")
            else:
                # Wrap around
                cursor = editor.textCursor()
                if forward:
                    cursor.movePosition(cursor.MoveOperation.Start)
                else:
                    cursor.movePosition(cursor.MoveOperation.End)
                editor.setTextCursor(cursor)
                found = editor.find(search_text, flags)
                
                if found:
                    results_label.setText("Match found (wrapped)")
                    results_label.setStyleSheet("color: #1f6feb; padding: 4px;")
                else:
                    results_label.setText("No matches found")
                    results_label.setStyleSheet("color: #f85149; padding: 4px;")
            
            return found
        
        def replace_text():
            cursor = editor.textCursor()
            if cursor.hasSelection():
                cursor.insertText(replace_box.text())
                find_text()  # Find next
        
        def replace_all_text():
            search_text = search_box.text()
            replace_text_val = replace_box.text()
            
            if not search_text:
                return
            
            # Get all text
            all_text = editor.toPlainText()
            
            # Count matches
            if case_check.isChecked():
                count = all_text.count(search_text)
            else:
                count = all_text.lower().count(search_text.lower())
            
            if count == 0:
                results_label.setText("No matches to replace")
                results_label.setStyleSheet("color: #f85149; padding: 4px;")
                return
            
            # Replace
            if case_check.isChecked():
                new_text = all_text.replace(search_text, replace_text_val)
            else:
                # Case insensitive replace
                import re
                pattern = re.compile(re.escape(search_text), re.IGNORECASE)
                new_text = pattern.sub(replace_text_val, all_text)
            
            editor.setPlainText(new_text)
            results_label.setText(f"Replaced {count} matches")
            results_label.setStyleSheet("color: #238636; padding: 4px;")
        
        # Connect signals
        find_next_btn.clicked.connect(lambda: find_text(True))
        find_prev_btn.clicked.connect(lambda: find_text(False))
        replace_btn.clicked.connect(replace_text)
        replace_all_btn.clicked.connect(replace_all_text)
        close_btn.clicked.connect(dialog.close)
        search_box.returnPressed.connect(lambda: find_text(True))
        
        # Focus search box and select current selection if any
        cursor = editor.textCursor()
        if cursor.hasSelection():
            search_box.setText(cursor.selectedText())
        search_box.setFocus()
        search_box.selectAll()
        
        dialog.show()
    
    def update_breadcrumb(self):
        """Update breadcrumb bar with current file path"""
        current_tab = self.tabs.currentWidget()
        
        if not current_tab or not hasattr(current_tab, 'file_path'):
            self.breadcrumb_bar.setText("No file open")
            return
        
        file_path = current_tab.file_path
        if not file_path:
            self.breadcrumb_bar.setText("Untitled")
            return
        
        # Show full path or relative path if in workspace
        if self.startup_folder and file_path.startswith(self.startup_folder):
            rel_path = os.path.relpath(file_path, self.startup_folder)
            display_path = f"/ > {rel_path.replace(os.sep, ' > ')}"
        else:
            display_path = f"{file_path}"
        
        self.breadcrumb_bar.setText(display_path)
        self.breadcrumb_bar.setToolTip(file_path)
            
            
            
    def __init__(self):
        super().__init__()
        self.setWindowTitle("cedit")
        self.resize(1000, 700)

        self.setWindowIcon(QtGui.QIcon('icon.png'))

        StatusManager.init(self.statusBar())

        # Performance optimizations
        self._file_cache = {}
        self._max_file_cache_size = 100
        self._recent_files_cache = set()
        
        # Register caches with memory manager
        memory_manager.register_cache(self._file_cache, max_size=50)

        # Load settings (may prompt for folder)
        self.load_settings()

        # Apply loaded settings to UI
        self.apply_theme(self.theme)
        # Tabs not yet created, but will be applied after tabs are added

        # Recent files tracking
        self.recent_files = []
        self.max_recent_files = 10

        # Sidebar: file browser
        self.model = QFileSystemModel()
        self.model.setRootPath("")
        self.tree = QTreeView()
        self.tree.setModel(self.model)
        # Always open the startup folder if set
        if self.startup_folder:
            self.tree.setRootIndex(self.model.index(self.startup_folder))
        else:
            self.tree.setRootIndex(self.model.index(QDir.currentPath()))

        for i in range(1, self.model.columnCount()):
            self.tree.hideColumn(i)
        self.tree.setHeaderHidden(True)
        self.tree.setColumnWidth(0, 250)
        self.tree.setRootIsDecorated(True)
        
        # Enable drag and drop for moving files/folders
        self.tree.setDragEnabled(True)
        self.tree.setAcceptDrops(True)
        self.tree.setDropIndicatorShown(True)
        self.tree.setDragDropMode(QTreeView.DragDropMode.InternalMove)
        self.model.setReadOnly(False)  # Allow file operations
        
        # Connect to model's file moved signal for status updates
        try:
            # This signal is emitted when files are moved via drag-and-drop
            from PyQt5.QtCore import QFileSystemWatcher
            self._file_watcher = QFileSystemWatcher()
        except:
            pass

        self.tree.clicked.connect(self.open_file_from_tree)
        self.tree.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self.show_sidebar_context_menu)
        
        # Add breadcrumb bar above tabs
        self.breadcrumb_bar = QLabel()
        self.breadcrumb_bar.setStyleSheet("""
            QLabel {
                background: #161b22;
                color: #8b949e;
                padding: 8px 12px;
                border-bottom: 1px solid #21262d;
                font-size: 12px;
                font-family: 'Consolas', monospace;
            }
        """)
        self.breadcrumb_bar.setText("No file open")
        self.breadcrumb_bar.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        self.breadcrumb_bar.setWordWrap(False)

        # Tabs for open files
        self.tabs = QTabWidget()
        self.tabs.setTabsClosable(True)
        self.tabs.tabCloseRequested.connect(self.close_tab)
        self.tabs.setMovable(True)
        self.tabs.currentChanged.connect(self.update_breadcrumb)
        
        # Configure tab bar for better text handling
        tab_bar = self.tabs.tabBar()
        if tab_bar:
            tab_bar.setElideMode(Qt.TextElideMode.ElideMiddle)  # Elide in middle to show extension
            tab_bar.setUsesScrollButtons(True)
            tab_bar.setExpanding(False)
            # Force fixed width per tab for consistent behavior
            from PyQt5.QtWidgets import QStyleOptionTab
            # Note: max-width is controlled by CSS, eliding handles long names
            
            # Enable middle-click to close tabs
            def tab_bar_mouse_release(event):
                if event.button() == Qt.MouseButton.MiddleButton:
                    index = tab_bar.tabAt(event.pos())
                    if index >= 0:
                        self.close_tab(index)
                else:
                    # Call the original mouse release event
                    tab_bar.__class__.mouseReleaseEvent(tab_bar, event)
            
            tab_bar.mouseReleaseEvent = tab_bar_mouse_release

        # Splitter for sidebar and editor
        splitter = QSplitter()
        splitter.addWidget(self.tree)
        
        # Right side container with breadcrumb and tabs
        right_container = QWidget()
        right_layout = QVBoxLayout(right_container)
        right_layout.setContentsMargins(0, 0, 0, 0)
        right_layout.setSpacing(0)
        right_layout.addWidget(self.breadcrumb_bar)
        right_layout.addWidget(self.tabs)
        
        splitter.addWidget(right_container)
        splitter.setSizes([200, 800])

        central_widget = QWidget()
        layout = QHBoxLayout(central_widget)
        layout.addWidget(splitter)
        self.setCentralWidget(central_widget)

        # Menu actions
        menubar = self.menuBar()
        file_menu = menubar.addMenu("File")

        open_folder_action = QAction("Open Folder", self)
        open_folder_action.setShortcut("Ctrl+O")
        open_folder_action.setStatusTip("Open a folder to browse files")
        open_folder_action.triggered.connect(self.open_folder)
        file_menu.addAction(open_folder_action)

        open_file_action = QAction("Open File", self)
        open_file_action.setShortcut("Ctrl+Shift+O")
        open_file_action.setStatusTip("Open a single file")
        open_file_action.triggered.connect(self.open_file_dialog)
        file_menu.addAction(open_file_action)

        new_file_action = QAction("New File", self)
        new_file_action.setShortcut("Ctrl+N")
        new_file_action.setStatusTip("Create a new file")
        new_file_action.triggered.connect(self.new_file)
        file_menu.addAction(new_file_action)

        save_file_action = QAction("Save", self)
        save_file_action.setShortcut("Ctrl+S")
        save_file_action.setStatusTip("Save the current file")
        save_file_action.triggered.connect(self.save_file)
        file_menu.addAction(save_file_action)

        saveas_file_action = QAction("Save As", self)
        saveas_file_action.setStatusTip("Save the current file with a new name")
        saveas_file_action.triggered.connect(self.save_file_as)
        file_menu.addAction(saveas_file_action)

        close_tab_action = QAction("Close Tab", self)
        close_tab_action.setShortcut("Ctrl+W")
        close_tab_action.setStatusTip("Close the current tab")
        close_tab_action.triggered.connect(lambda: self.close_tab(self.tabs.currentIndex()))
        file_menu.addAction(close_tab_action)

        # Recent Files menu
        if menubar:
            self.recent_menu = menubar.addMenu("Recent Files")
            self.update_recent_files_menu()

        # Status bar
        self.status = self.statusBar()
        StatusManager.show_message("Welcome!")

        # Setup shortcuts
        self.setup_shortcuts()

    def open_file_dialog(self):
        file_path, _ = QFileDialog.getOpenFileName(self, "Open File", QDir.currentPath())
        if file_path:
            self.open_file(file_path)

    def update_recent_files_menu(self):
        if not self.recent_menu:
            return
        self.recent_menu.clear()
        for file_path in self.recent_files:
            action = QAction(file_path, self)
            action.triggered.connect(lambda checked, fp=file_path: self.open_file(fp))
            self.recent_menu.addAction(action)
        if not self.recent_files:
            self.recent_menu.addAction(QAction("No recent files", self))

    def add_to_recent_files(self, file_path):
        if file_path in self._recent_files_cache:
            return  # Already in cache, skip update
        
        if file_path in self.recent_files:
            self.recent_files.remove(file_path)
        self.recent_files.insert(0, file_path)
        if len(self.recent_files) > self.max_recent_files:
            removed = self.recent_files.pop()
            self._recent_files_cache.discard(removed)
        self._recent_files_cache.add(file_path)
        self.update_recent_files_menu()
    def new_file(self):
        new_tab = EditorTab()
        self.tabs.addTab(new_tab, "Untitled")
        self.tabs.setCurrentWidget(new_tab)
        StatusManager.show_message("New file created.")

    def save_file(self):
        tab = self.tabs.currentWidget()
        if tab and hasattr(tab, 'editor'):
            if tab.file_path:
                try:
                    with open(tab.file_path, 'w+', encoding='utf-8') as f:
                        f.write(tab.editor.toPlainText())
                    StatusManager.show_message("Saved:", tab.file_path)
                    if hasattr(tab, "mark_saved"):
                        tab.mark_saved()
                    self.update_tab_title_modified(tab)
                except Exception as e:
                    StatusManager.show_message(f"Error saving file: {e}")
            else:
                self.save_file_as()

    def save_file_as(self):
        tab = self.tabs.currentWidget()
        if tab and hasattr(tab, 'editor'):
            file_path, _ = QFileDialog.getSaveFileName(self, "Save File As", QDir.currentPath())
            if file_path:
                try:
                    with open(file_path, 'w+', encoding='utf-8') as f:
                        f.write(tab.editor.toPlainText())
                    tab.file_path = file_path
                    if hasattr(tab, "mark_saved"):
                        tab.mark_saved()
                    self.update_tab_title_modified(tab)
                    StatusManager.show_message("Saved as:", file_path)
                except Exception as e:
                    StatusManager.show_message(f"Error saving file: {e}")

    def open_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Open Folder", QDir.currentPath())
        if folder:
            self.tree.setRootIndex(self.model.index(folder))
            self.startup_folder = folder
            self.save_settings()

    def open_file_from_tree(self, index):
        file_path = self.model.filePath(index)
        if self.model.isDir(index):
            # Check if it's an Assets folder at root level
            folder_name = os.path.basename(file_path).lower()
            if folder_name == "assets" and self.is_root_level_folder(file_path):
                self.open_assets_browser(file_path)
        else:
            self.open_file(file_path)
    
    def is_root_level_folder(self, folder_path):
        """Check if folder is at root level of workspace"""
        if not self.startup_folder:
            return False
        
        # Normalize paths
        folder_path = os.path.normpath(folder_path)
        startup_folder = os.path.normpath(self.startup_folder)
        
        # Get parent of the folder
        parent = os.path.dirname(folder_path)
        
        # Check if parent is the startup folder
        return os.path.normpath(parent) == startup_folder
    
    def open_assets_browser(self, folder_path):
        """Open the enhanced asset browser for an Assets folder"""
        # Check if already open
        for i in range(self.tabs.count()):
            tab = self.tabs.widget(i)
            if isinstance(tab, AssetBrowserTab) and tab.folder_path == folder_path:
                self.tabs.setCurrentIndex(i)
                return
        
        # Create new asset browser tab
        asset_tab = AssetBrowserTab(folder_path)
        tab_name = f"🎨 {os.path.basename(folder_path)}"
        self.tabs.addTab(asset_tab, tab_name)
        self.tabs.setTabToolTip(self.tabs.count()-1, folder_path)
        self.tabs.setCurrentWidget(asset_tab)
        StatusManager.show_message("Opened Assets browser:", folder_path)

    def open_file(self, file_path):
        # Check if already open
        for i in range(self.tabs.count()):
            tab = self.tabs.widget(i)
            if tab and hasattr(tab, 'file_path') and tab.file_path == file_path:
                self.tabs.setCurrentIndex(i)
                self.update_breadcrumb()  # Update breadcrumb when switching to existing tab
                return
        
        # Check file cache
        if file_path in self._file_cache:
            file_info = self._file_cache[file_path]
        else:
            # Cache file info
            file_info = {
                'ext': os.path.splitext(file_path)[1].lower(),
                'name': os.path.basename(file_path),
                'exists': os.path.exists(file_path)
            }
            # Limit cache size
            if len(self._file_cache) >= self._max_file_cache_size:
                oldest_key = next(iter(self._file_cache))
                del self._file_cache[oldest_key]
            self._file_cache[file_path] = file_info
        
        if not file_info['exists']:
            StatusManager.show_message(f"File not found: {file_path}")

            return
            
        ext = file_info['ext']
        if ext == '.md':
            new_tab = MarkdownTab(file_path)
        elif ext in ['.png', '.jpg', '.jpeg', '.bmp', '.gif', '.webp']:
            new_tab = ImageTab(file_path)
        elif ext == '.pdf':
            new_tab = PDFTab(file_path)
        else:
            new_tab = EditorTab(file_path)
        
        # Shorten tab name if too long
        tab_name = self._shorten_filename(file_info['name'], max_length=13)
        self.tabs.addTab(new_tab, tab_name)
        self.tabs.setTabToolTip(self.tabs.count()-1, file_path)
        self.tabs.setCurrentWidget(new_tab)
        self.update_breadcrumb()  # Update breadcrumb for new file
        StatusManager.show_message("Opened:", file_path)
        self.add_to_recent_files(file_path)
    
    def show_quick_open(self):
        """Show quick open dialog to navigate and open files"""
        if not self.startup_folder:
            QMessageBox.information(self, "Quick Open", "Please open a folder first (Ctrl+O)")
            return
        
        # Create dialog
        dialog = QDialog(self)
        dialog.setWindowTitle("Quick Open")
        dialog.setMinimumWidth(600)
        dialog.setMinimumHeight(400)
        
        layout = QVBoxLayout(dialog)
        
        # Search box
        search_box = QLineEdit()
        search_box.setPlaceholderText("Type to filter files...")
        layout.addWidget(search_box)
        
        # File list
        from PyQt5.QtWidgets import QListWidget, QListWidgetItem
        file_list = QListWidget()
        file_list.setAlternatingRowColors(True)
        file_list.setStyleSheet("""
            QListWidget {
                background-color: #0d1117;
                alternate-background-color: #161b22;
                color: #e6edf3;
                border: 1px solid #30363d;
                border-radius: 6px;
                padding: 4px;
            }
            QListWidget::item {
                padding: 8px;
                border-radius: 4px;
            }
            QListWidget::item:selected {
                background-color: #1f6feb;
                color: #ffffff;
            }
            QListWidget::item:hover:!selected {
                background-color: #21262d;
            }
        """)
        layout.addWidget(file_list)
        
        # Buttons
        button_layout = QHBoxLayout()
        button_layout.addStretch()
        open_btn = QPushButton("Open")
        cancel_btn = QPushButton("Cancel")
        button_layout.addWidget(open_btn)
        button_layout.addWidget(cancel_btn)
        layout.addLayout(button_layout)
        
        # Collect all files recursively
        all_files = []
        def collect_files(folder):
            try:
                for root, dirs, files in os.walk(folder):
                    dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['__pycache__', 'node_modules', 'venv', 'env']]
                    for file in files:
                        if not file.startswith('.'):
                            full_path = os.path.join(root, file)
                            rel_path = os.path.relpath(full_path, folder)
                            all_files.append((rel_path, full_path))
            except Exception:
                pass
        
        collect_files(self.startup_folder)
        all_files.sort()
        
        # Populate list
        def update_list(filter_text=""):
            file_list.clear()
            filter_lower = filter_text.lower()
            for rel_path, full_path in all_files:
                if not filter_text or filter_lower in rel_path.lower():
                    item = QListWidgetItem(rel_path)
                    item.setData(Qt.ItemDataRole.UserRole, full_path)
                    file_list.addItem(item)
            if file_list.count() > 0:
                file_list.setCurrentRow(0)
        
        update_list()
        
        # Connect signals
        search_box.textChanged.connect(update_list)
        
        def open_selected():
            current_item = file_list.currentItem()
            if current_item:
                file_path = current_item.data(Qt.ItemDataRole.UserRole)
                self.open_file(file_path)
                dialog.accept()
        
        open_btn.clicked.connect(open_selected)
        cancel_btn.clicked.connect(dialog.reject)
        file_list.itemDoubleClicked.connect(lambda: open_selected())
        
        # Handle Enter key
        def handle_key_press(e):
            from PyQt5.QtCore import Qt
            if e and e.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                open_selected()
            else:
                QListWidget.keyPressEvent(file_list, e)
        
        file_list.keyPressEvent = handle_key_press
        
        # Focus search box
        search_box.setFocus()
        
        dialog.exec_()
        
    def show_welcome_tab(self):
        if self.tabs.count() == 0:
            from PyQt5.QtWidgets import QPushButton, QGridLayout, QSizePolicy, QTextBrowser

            welcome_tab = QWidget()
            main_layout = QVBoxLayout(welcome_tab)
            main_layout.setContentsMargins(80, 80, 80, 80)
            main_layout.setSpacing(40)

            # ─── Header ───────────────────────────────────────
            title = QLabel("<b style='color:#58a6ff; font-size: 48px;'>cedit</b>")
            title.setAlignment(Qt.AlignmentFlag.AlignCenter)
            title.setStyleSheet("""
                font-size: 48px; 
                font-weight: 300; 
                letter-spacing: 2px;
            """)
            main_layout.addWidget(title)

            subtitle = QLabel("A modern, lightweight code & markdown editor")
            subtitle.setAlignment(Qt.AlignmentFlag.AlignCenter)
            subtitle.setStyleSheet("""
                color: #8b949e; 
                font-size: 18px; 
                font-weight: 400;
                margin-bottom: 20px;
            """)
            main_layout.addWidget(subtitle)

            # ─── Action Cards Grid ────────────────────────────
            grid = QGridLayout()
            grid.setSpacing(16)
            grid.setContentsMargins(40, 20, 40, 20)

            button_style = """
                QPushButton {
                    background: qlineargradient(x1:0, y1:0, x2:0, y2:1,
                                                stop:0 #21262d, stop:1 #161b22);
                    color: #e6edf3;
                    font-size: 15px;
                    font-weight: 500;
                    padding: 20px;
                    border: 1px solid #30363d;
                    border-radius: 12px;
                    text-align: center;
                }
                QPushButton:hover {
                    background: qlineargradient(x1:0, y1:0, x2:0, y2:1,
                                                stop:0 #30363d, stop:1 #21262d);
                    border-color: #58a6ff;
                }
                QPushButton:pressed {
                    background: #161b22;
                }
            """

            # Define buttons as (row, col, icon, text, callback)
            actions = [
                (0, 0, "📂", "Open Folder", self.open_folder),
                # (0, 1, "⚙️", "Settings", self.open_settings),
            ]

            for row, col, icon, text, callback in actions:
                btn = QPushButton(f"{icon}  {text}")
                btn.setStyleSheet(button_style)
                btn.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
                btn.setMinimumHeight(100)
                btn.clicked.connect(callback)
                grid.addWidget(btn, row, col)

            main_layout.addLayout(grid)
            main_layout.addStretch()
            
            # Add keyboard shortcuts section
            shortcuts_frame = QFrame()
            shortcuts_frame.setStyleSheet("""
                QFrame {
                    background: #161b22;
                    border: 1px solid #30363d;
                    border-radius: 8px;
                    padding: 16px;
                }
            """)
            shortcuts_layout = QVBoxLayout(shortcuts_frame)
            
            shortcuts_title = QLabel("<b style='color:#58a6ff;'>⌨️ Keyboard Shortcuts</b>")
            shortcuts_title.setStyleSheet("font-size: 16px; margin-bottom: 8px;")
            shortcuts_layout.addWidget(shortcuts_title)
            
            shortcuts_text = """
            <table style='color: #e6edf3; font-size: 12px;'>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+O</b></td><td style='padding: 4px;'>Open Folder</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+Shift+O</b></td><td style='padding: 4px;'>Open File</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+N</b></td><td style='padding: 4px;'>New File</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+S</b></td><td style='padding: 4px;'>Save</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+W</b></td><td style='padding: 4px;'>Close Tab</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+L</b></td><td style='padding: 4px;'>Quick Open</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+P</b></td><td style='padding: 4px;'>Command Palette</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+F</b></td><td style='padding: 4px;'>Find in File</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+Shift+F</b></td><td style='padding: 4px;'>Find in Files</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+G</b></td><td style='padding: 4px;'>Go to Line</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>Ctrl+Tab</b></td><td style='padding: 4px;'>Next Tab</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>F5</b></td><td style='padding: 4px;'>Reload Folder</td></tr>
                <tr><td style='padding: 4px 12px; color: #8b949e;'><b>F11</b></td><td style='padding: 4px;'>Toggle Fullscreen</td></tr>
            </table>
            """
            
            shortcuts_label = QLabel(shortcuts_text)
            shortcuts_label.setStyleSheet("color: #e6edf3;")
            shortcuts_label.setWordWrap(True)
            shortcuts_layout.addWidget(shortcuts_label)
            
            # main_layout.addWidget(shortcuts_frame)
            
            # Add recent files section if any
            if self.recent_files:
                recent_frame = QFrame()
                recent_frame.setStyleSheet("""
                    QFrame {
                        background: #161b22;
                        border: 1px solid #30363d;
                        border-radius: 8px;
                        padding: 16px;
                    }
                """)
                recent_layout = QVBoxLayout(recent_frame)
                
                recent_title = QLabel("<b style='color:#58a6ff;'>📚 Recent Files</b>")
                recent_title.setStyleSheet("font-size: 16px; margin-bottom: 8px;")
                recent_layout.addWidget(recent_title)
                
                for file_path in self.recent_files[:5]:  # Show only last 5
                    file_btn = QPushButton(f"📄 {os.path.basename(file_path)}")
                    file_btn.setStyleSheet("""
                        QPushButton {
                            background: transparent;
                            color: #58a6ff;
                            border: none;
                            text-align: left;
                            padding: 8px;
                            font-size: 13px;
                        }
                        QPushButton:hover {
                            background: #21262d;
                            border-radius: 4px;
                        }
                    """)
                    file_btn.setToolTip(file_path)
                    file_btn.clicked.connect(lambda checked, fp=file_path: self.open_file(fp))
                    recent_layout.addWidget(file_btn)
                
                # main_layout.addWidget(recent_frame)

            self.tabs.addTab(welcome_tab, "Dashboard")
            self.tabs.setCurrentWidget(welcome_tab)
            
    def close_tab(self, index):
        if index < 0 or index >= self.tabs.count():
            return

        tab = self.tabs.widget(index)
        
        # Check for unsaved changes
        if tab and hasattr(tab, 'is_modified') and callable(tab.is_modified) and tab.is_modified():
            file_name = "Untitled"
            if hasattr(tab, 'file_path') and tab.file_path:
                file_name = os.path.basename(tab.file_path)
            
            msg_box = QMessageBox(self)
            msg_box.setWindowTitle("Unsaved Changes")
            msg_box.setText(f"'{file_name}' has unsaved changes.\n\nDo you want to save before closing?")
            msg_box.setStandardButtons(QMessageBox.StandardButton.Save | QMessageBox.StandardButton.Discard | QMessageBox.StandardButton.Cancel)
            msg_box.setDefaultButton(QMessageBox.StandardButton.Save)
            reply = msg_box.exec_()
            
            if reply == QMessageBox.StandardButton.Save:
                # Save the file
                self.tabs.setCurrentIndex(index)
                self.save_file()
                # Check if save was successful (file_path should be set)
                if not hasattr(tab, 'file_path') or not tab.file_path:
                    return  # Save was cancelled
            elif reply == QMessageBox.StandardButton.Cancel:
                return  # Don't close the tab

        # 1️⃣ Call custom cleanup if the tab has it
        if tab and hasattr(tab, "close_tab") and callable(tab.close_tab):
            tab.close_tab()  # e.g., ImageTab, PDFTab

        # 2️⃣ Delete the tab widget to release memory
        self.tabs.removeTab(index)
        if tab:
            tab.deleteLater()

        # 3️⃣ Show welcome tab if no tabs left
        if self.tabs.count() == 0:
            self.show_welcome_tab()
        
        # Update breadcrumb after closing tab
        self.update_breadcrumb()
    
    def closeEvent(self, a0):
        """Handle application close event"""
        file_worker.stop()
        
        # Clear all caches
        self._file_cache.clear()
        self._recent_files_cache.clear()
        
        # Force garbage collection
        gc.collect()
        
        # Accept the close event
        if a0:
            a0.accept()

def cleanup_memory():
    """Clean up memory and run garbage collection"""
    gc.collect()
    # Force garbage collection multiple times for better cleanup
    for _ in range(3):
        gc.collect()

def main():
    from PyQt5.QtCore import QCoreApplication, Qt
    QCoreApplication.setAttribute(Qt.ApplicationAttribute.AA_ShareOpenGLContexts)
    
    # Set up memory management
    QCoreApplication.setAttribute(Qt.ApplicationAttribute.AA_EnableHighDpiScaling, True)
    QCoreApplication.setAttribute(Qt.ApplicationAttribute.AA_UseHighDpiPixmaps, True)

    # Global exception hook for uncaught exceptions
    def excepthook(type_, value, tb):
        error_msg = f"{value}\n\n{''.join(traceback.format_exception(type_, value, tb))}"
        from PyQt5.QtWidgets import QMessageBox, QApplication
        app = QApplication.instance() or QApplication([])
        msg_box = QMessageBox()
        msg_box.setIcon(QMessageBox.Critical)
        msg_box.setWindowTitle("Application Error")
        msg_box.setText("An unhandled exception occurred.")
        msg_box.setDetailedText(error_msg)
        msg_box.exec_()
        
        # Cleanup on error
        try:
            file_worker.stop()
            cleanup_memory()
        except:
            pass
        sys.exit(1)
    sys.excepthook = excepthook
    
    try:
        app = QApplication(sys.argv)
        app.setWindowIcon(QIcon('icon.png'))
        
        # Set up periodic memory cleanup (reduced frequency since we have memory manager)
        cleanup_timer = QTimer()
        cleanup_timer.timeout.connect(cleanup_memory)
        cleanup_timer.start(60000)  # Clean up every 60 seconds
        
        window = MainWindow()
        window.show()
        window.show_welcome_tab()
        window.apply_settings_to_editors()
        
        # Center window on screen
        qr = window.frameGeometry()
        screen = window.screen()
        if screen:
            cp = screen.availableGeometry().center()
            qr.moveCenter(cp)
            window.move(qr.topLeft())
        
        exit_code = app.exec_()
        
        # Final cleanup
        file_worker.stop()
        cleanup_memory()
        
    except Exception as e:
        from PyQt5.QtWidgets import QMessageBox
        error_msg = f"{str(e)}\n\n{traceback.format_exc()}"
        msg_box = QMessageBox()
        msg_box.setIcon(QMessageBox.Critical)
        msg_box.setWindowTitle("Application Error")
        msg_box.setText("An error occurred while running the application.")
        msg_box.setDetailedText(error_msg)
        msg_box.exec_()
        
        # Cleanup on error
        try:
            file_worker.stop()
            cleanup_memory()
        except:
            pass
        exit_code = 1
    sys.exit(exit_code)

if __name__ == "__main__":
    main()
