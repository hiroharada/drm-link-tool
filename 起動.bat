@echo off
chcp 932 > nul
echo DRMリンク拾いツールを起動します。終了するときはこのウィンドウを閉じてください。
rem ----------------------------------------------------------
rem  共有フォルダから直接動かすと遅いので、ツール一式をこのPCに
rem  コピー(変更分だけ)してから起動する。
rem  変換済みデータ(_cache)は使うDRM版の分だけ、ツールが必要になった時にコピーする。
rem  DRMデータは共有フォルダを参照。
rem ----------------------------------------------------------
set "TOOL=%~dp0"
set "TOOL=%TOOL:~0,-1%"
rem ツール本体(プログラム・変換済みデータ・利用ログ)はこのサブフォルダにある
set "SRC=%TOOL%\30_ツール本体（触らない）"
set "DATA=%TOOL%\..\DRMコピー_こっちを使う"
set "LOCAL=%LOCALAPPDATA%\DRMリンク拾いツール"

echo [準備] ツールをこのPCにコピーしています（初回は数十秒、2回目以降は数秒）...
robocopy "%SRC%" "%LOCAL%" /MIR /XD __pycache__ _cache _利用ログ /XF *.tmp *.bat /R:1 /W:1 /NFL /NDL /NJH /NJS /NP > nul
if errorlevel 8 (
  echo [準備] このPCへのコピーに失敗したため、共有フォルダから直接起動します（遅くなります）
  set "LOCAL=%SRC%"
)

set "PY=%LOCAL%\python\python.exe"
if not exist "%PY%" set "PY=python"
echo [準備] 起動中...ブラウザに進捗が表示されます
"%PY%" -X utf8 "%LOCAL%\server.py" "%DATA%" "--shared-cache=%SRC%\_cache" %*
if errorlevel 1 pause
