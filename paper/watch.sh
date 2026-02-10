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
latexmk -pdf -pvc -interaction=nonstopmode -file-line-error -f scratch.tex &

# Wait for PDFs to exist, then configure Skim
(
  PAPER_DIR="$(cd "$(dirname "$0")" && pwd)"
  MAIN_PDF="$PAPER_DIR/main.pdf"
  SCRATCH_PDF="$PAPER_DIR/scratch.pdf"

  # Wait for both PDFs to be generated
  while [ ! -f "$MAIN_PDF" ] || [ ! -f "$SCRATCH_PDF" ]; do
    sleep 1
  done

  # Give Skim a moment to open them
  sleep 2

  # Configure Skim: full screen, auto-resize zoom
  osascript <<EOF
tell application "Skim"
    activate

    open POSIX file "$MAIN_PDF"
    open POSIX file "$SCRATCH_PDF"

    delay 1

    -- Set auto-resize zoom via view settings
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

        -- Get window names from Window menu (they appear at the end)
        set winMenuItems to name of every menu item of menu "Window" of menu bar 1
        set win1 to ""
        set win2 to ""
        repeat with itemName in winMenuItems
            if itemName contains ".pdf" then
                if win1 is "" then
                    set win1 to itemName as string
                else
                    set win2 to itemName as string
                end if
            end if
        end repeat

        -- Switch to second window FIRST (so menu bar stays with non-fullscreen window after)
        if win2 is not "" then
            click menu item win2 of menu "Window" of menu bar 1
            delay 0.3
        end if

        -- Full screen second window (now active)
        click menu item "Full Screen" of menu "View" of menu bar 1
        delay 1.5

        -- Switch back to first window via Window menu and full screen it
        if win1 is not "" then
            click menu item win1 of menu "Window" of menu bar 1
            delay 0.5
            click menu item "Full Screen" of menu "View" of menu bar 1
        end if
    end tell
end tell
EOF

  echo "Skim configured: full screen + auto-resize"
) &

wait
