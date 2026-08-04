[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [ValidateScript({ Test-Path -LiteralPath $_ -PathType Leaf })]
    [string]$Package,
    [string]$RouterHost = "192.168.8.1",
    [string]$RouterUser = "root",
    [string]$HostKey = "",
    [string]$Password = "",
    [string]$FactorySsid = "",
    [string]$FactoryWifiPassword = ""
)

$ErrorActionPreference = "Stop"

function Find-PuttyTool([string]$Name) {
    $command = Get-Command $Name -ErrorAction SilentlyContinue
    if ($command) { return $command.Source }
    $candidate = Join-Path $env:ProgramFiles "PuTTY\$Name.exe"
    if (Test-Path -LiteralPath $candidate) { return $candidate }
    throw "$Name.exe not found; install PuTTY or add it to PATH"
}

function Quote-Remote([string]$Value) {
    return "'" + ($Value -replace "'", "'\''") + "'"
}

$packagePath = (Resolve-Path -LiteralPath $Package).Path
if (-not $packagePath.EndsWith(".tar.gz", [StringComparison]::OrdinalIgnoreCase)) {
    throw "Package must be a .tar.gz artifact"
}
$checksumPath = "$packagePath.sha256"
if (-not (Test-Path -LiteralPath $checksumPath -PathType Leaf)) {
    throw "Adjacent checksum file is missing: $checksumPath"
}
if (($FactorySsid -eq "") -xor ($FactoryWifiPassword -eq "")) {
    throw "FactorySsid and FactoryWifiPassword must be supplied together"
}

$pscp = Find-PuttyTool "pscp"
$plink = Find-PuttyTool "plink"
$authArgs = @("-ssh")
if ($HostKey) { $authArgs += @("-batch", "-hostkey", $HostKey) }
if ($Password) { $authArgs += @("-pw", $Password) }
$target = "${RouterUser}@${RouterHost}"
$remotePackage = "/tmp/" + [IO.Path]::GetFileName($packagePath)

Write-Host "Uploading verified package to $target ..."
& $pscp -scp @authArgs $packagePath $checksumPath "${target}:/tmp/"
if ($LASTEXITCODE -ne 0) { throw "Package upload failed" }

$commands = @(
    "set -eu",
    "archive=" + (Quote-Remote $remotePackage),
    "if command -v light-rid-upgrade >/dev/null 2>&1; then light-rid-upgrade `"`$archive`"; else tar -xzf `"`$archive`" -C /; light-rid-install; fi"
)
if ($FactorySsid) {
    $commands += "LIGHT_RID_FACTORY_SSID=" + (Quote-Remote $FactorySsid) + " LIGHT_RID_FACTORY_WIFI_PASSWORD=" + (Quote-Remote $FactoryWifiPassword) + " light-rid-install --factory-provision"
}
$commands += @(
    "sleep 12",
    "light-rid-run check",
    "light-rid-run status",
    "/etc/init.d/light-rid enabled",
    "netstat -ln | grep -q ':4600[[:space:]]'",
    "iw dev ridmon info | grep -q 'type monitor'",
    "iw dev ridmon info | grep -q 'channel 6 '"
)

Write-Host "Installing and enabling Light RID ..."
& $plink @authArgs $target ($commands -join "; ")
if ($LASTEXITCODE -ne 0) { throw "Remote deployment failed" }
Write-Host "Deployment complete: http://${RouterHost}:4600/"
