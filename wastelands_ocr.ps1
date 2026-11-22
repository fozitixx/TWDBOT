$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [Text.UTF8Encoding]::new($false)
Add-Type -AssemblyName System.Runtime.WindowsRuntime
$null = [Windows.Media.Ocr.OcrEngine,Windows.Foundation,ContentType=WindowsRuntime]
$null = [Windows.Graphics.Imaging.BitmapDecoder,Windows.Graphics.Imaging,ContentType=WindowsRuntime]
$null = [Windows.Graphics.Imaging.SoftwareBitmap,Windows.Graphics.Imaging,ContentType=WindowsRuntime]
$null = [Windows.Globalization.Language,Windows.Globalization,ContentType=WindowsRuntime]
$await = [System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
    $_.Name -eq 'AsTask' -and $_.IsGenericMethod -and $_.GetGenericArguments().Length -eq 1 -and
    $_.GetParameters().Length -eq 1 -and $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1'
} | Select-Object -First 1
function Wait-WinRT($op,$type) {
    $task = $await.MakeGenericMethod($type).Invoke($null,@($op))
    if (!$task.Wait(6000)) { throw 'Windows OCR timeout' }
    $task.GetAwaiter().GetResult()
}
$engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromLanguage([Windows.Globalization.Language]::new('en-US'))
if (!$engine) { $engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromUserProfileLanguages() }
while ($null -ne ($line = [Console]::ReadLine())) {
    $bitmap = $null
    $stream = $null
    $ms = $null
    try {
        if (!$engine) { throw 'Install Windows English OCR language support' }
        $ms = [IO.MemoryStream]::new([Convert]::FromBase64String($line))
        $stream = [System.IO.WindowsRuntimeStreamExtensions]::AsRandomAccessStream($ms)
        $decoder = Wait-WinRT ([Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($stream)) ([Windows.Graphics.Imaging.BitmapDecoder])
        $bitmap = Wait-WinRT ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap])
        $result = Wait-WinRT ($engine.RecognizeAsync($bitmap)) ([Windows.Media.Ocr.OcrResult])
        $words = @(foreach ($row in $result.Lines) {
            foreach ($word in $row.Words) {
                $r = $word.BoundingRect
                ,@($word.Text,$r.X,$r.Y,$r.Width,$r.Height)
            }
        })
        [Console]::WriteLine((ConvertTo-Json -Compress -Depth 5 @{words=$words}))
    } catch {
        [Console]::WriteLine((ConvertTo-Json -Compress @{error=$_.Exception.Message}))
    } finally {
        if ($bitmap) { $bitmap.Dispose() }
        if ($stream) { $stream.Dispose() }
        if ($ms) { $ms.Dispose() }
    }
}
