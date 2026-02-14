#!/bin/sh
# Continuous LaTeX compilation with auto-reload
# Run from the paper/ directory
# Stop with Ctrl-C

export PATH="$PATH:/Library/TeX/texbin"

# Clean up background jobs and Skim on exit
cleanup() {
    kill $(jobs -p) 2>/dev/null
    osascript -e 'tell application "Skim" to quit' 2>/dev/null
}
trap cleanup EXIT INT TERM

# -interaction=nonstopmode: don't stop on errors
# -file-line-error: better error messages
# -pvc: preview continuously
# -f: force processing past errors
latexmk -pdf -pvc -interaction=nonstopmode -file-line-error -f main.tex &

# Wait for PDF to exist, then configure Skim
(
  PAPER_DIR="$(cd "$(dirname "$0")" && pwd)"
  MAIN_PDF="$PAPER_DIR/main.pdf"

  while [ ! -f "$MAIN_PDF" ]; do
    sleep 1
  done

  sleep 2

  osascript <<EOF
tell application "Skim"
    activate
    open POSIX file "$MAIN_PDF"
    delay 1
    repeat with doc in documents
        tell doc
            set view settings to {auto scales:true}
        end tell
    end repeat
end tell

tell application "System Events"
    tell process "Skim"
        set frontmost to true
        delay 0.3
        click menu item "Full Screen" of menu "View" of menu bar 1
    end tell
end tell
EOF

  echo "Skim configured: full screen + auto-resize"
) &

wait
