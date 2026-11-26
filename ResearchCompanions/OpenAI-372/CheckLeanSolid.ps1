param(
    [Parameter(ParameterSetName = 'Bridge')][switch]$BridgeOnly,
    [Parameter(ParameterSetName = 'Module', Mandatory)][ValidatePattern('^[A-Za-z]+$')]
    [string]$ThroughModule,
    [switch]$GenerateOnly
)

$ErrorActionPreference = 'Stop'
$paperRoot = Join-Path $PSScriptRoot 'lean'
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '../..')).Path
$seen = [System.Collections.Generic.HashSet[string]]::new()
$sources = [System.Collections.Generic.List[string]]::new()

function Add-UpstreamModule([string]$ModuleName) {
    if (-not $seen.Add($ModuleName)) { return }
    $relativePath = $ModuleName.Replace('.', '/') + '.lean'
    $source = Get-Content -LiteralPath (Join-Path $paperRoot $relativePath) -Raw
    $imports = [regex]::Matches($source, '(?m)^import[ \t]+([^\r\n]+)')
    foreach ($line in $imports) {
        foreach ($name in ($line.Groups[1].Value -split '\s+')) {
            if ($name.StartsWith('OAI.')) { Add-UpstreamModule $name }
        }
    }
    $source = [regex]::Replace($source, '(?m)^import[^\r\n]*(\r?\n|$)', '')
    if ($ModuleName -eq 'OAI.MathematicalPhysics.Elasticity.Restriction') {
        $source = $source.Replace('memLp_indicator_iff_restrict hs',
            'memLp_indicator_iff_restrict hs.nullMeasurableSet')
        $source = $source.Replace('(μ := μ) hs).mpr (Lp.memLp f)',
            '(μ := μ) hs.nullMeasurableSet).mpr (Lp.memLp f)')
        $source = $source.Replace('eLpNorm_indicator_eq_eLpNorm_restrict hs',
            'eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet')
    }
    switch ($ModuleName.Split('.')[-1]) {
        'Carleman' {
            $source = $source -replace '  congr 1\r?\n  refine Fin.cases \?_ \(fun i => \?_\) i',
                "  apply congrArg (fun y : Smooth => -(((h^2 : ℝ) : ℂ) • y))`n  refine Fin.cases ?_ (fun i => ?_) i"
        }
        'Regularity' {
            $oldCalc = '  calc\r?\n    _ = ∫ x : E, φ x • 𝓕⁻ \(v : E → F\) x := by'
            $source = $source -replace $oldCalc,
                "  refine Eq.trans (b := ∫ x : E, φ x • 𝓕⁻ (v : E → F) x) ?_ ?_`n  ·"
            $source = $source.Replace('    _ = ∫ x : E, (𝓕⁻ φ) x • v x := by', '  ·')
            $source = $source -replace '    _ = _ := rfl\r?\n  rfl\r?\n\r?\n/-- A tempered distribution',
                "`n/-- A tempered distribution"
        }
        'Solvability' {
            $source = $source -replace '  congr 1\r?\n  · rw \[Finset.sum_comm\]\r?\n  · congr 1\r?\n    rw \[Finset.sum_comm\]',
                "  refine congrArg₂ (fun a b : ℂ => a + b) ?_ ?_`n  · rw [Finset.sum_comm]`n  · refine congrArg₂ (fun a b : ℂ => a + b) rfl ?_`n    rw [Finset.sum_comm]"
        }
        'CGO' {
            $source = $source.Replace('/-- A nested-cutoff interior norm estimate',
                "set_option maxHeartbeats 4000000 in`n/-- A nested-cutoff interior norm estimate")
            $source = $source -replace '    congr 1\r?\n    apply Finset.sum_congr rfl\r?\n    intro i _\r?\n    have hdi',
                "    refine congrArg₂ (fun a b : 𝓢'(E,ℂ) => a + b) rfl ?_`n    apply Finset.sum_congr rfl`n    intro i _`n    have hdi"
            $source = $source -replace '  calc\r?\n    K\*\(‖M f‖\+‖N g\+A f‖\) ≤ .+ := mul_le_mul_of_nonneg_left hsum hK.le\r?\n    _ = _ := by ring',
                '  exact (mul_le_mul_of_nonneg_left hsum hK.le).trans_eq (by ring)'
            $source = $source.Replace('(hMf ▸ hsource.symm)',
                '((congrArg (fun w : 𝓢''(E,ℂ) => Δ w) hMf).trans hsource.symm)')
        }
        { $_ -in 'BoundaryCalculus', 'BoundaryCharts' } {
            $body = "  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ψ x v) :=`n" +
                "    (hψ.fderiv_right (by simp)).clm_apply contDiff_const`n" +
                "  exact contDiff_pi.mp hd α"
            $source = $source -replace '\(jac ψ v α\) :=\s+\(contDiff_apply ℝ ℝ α\)\.comp \(\(hψ.fderiv_right \(by simp\)\)\.clm_apply contDiff_const\)',
                "(jac ψ v α) := by`n$body"
            $source = $source -replace '  exact contDiff_apply ℝ ℝ α \|>\.comp \(\(hψ.fderiv_right \(by simp\)\)\.clm_apply contDiff_const\)', $body
        }
        'BoundaryLayers' {
            $source = $source -replace '\(x := 1\) \(by norm_num\)\s+\(hg.of_le \(mod_cast le_top\)\).contDiffOn \(by simp\) hbound',
                '(x := 1) (hg.of_le (mod_cast le_top)).contDiffOn (by simp) hbound'
            $source = $source -replace '(simp only \[map_mul, Polynomial.eval_mul, hp\]\r?\n)      congr 1',
                '$1      refine congrArg₂ (fun a b : MP => a * b) rfl ?_'
            $source = $source -replace '  congr 1\r?\n  · rw \[shuffle5, Finset.sum_comm\]',
                "  refine congrArg₂ (fun a b : ℂ => a + b) ?_ ?_`n  · rw [shuffle5, Finset.sum_comm]"
        }
        'BoundarySymbols' {
            $source = $source -replace 'simp only \[Polynomial.coeff_monomial\]\s+split_ifs <;> simp',
                'simp only [Polynomial.coeff_monomial_apply]; split_ifs <;> simp'
            $source = $source.Replace('Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]',
                'Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]')
        }
        { $_ -in 'BoundaryData', 'BoundaryEnergy' } {
            $source = $source.Replace(
                'simp [amplitude,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]',
                "simp only [amplitude, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]`n  simp")
            if ($ModuleName.EndsWith('.BoundaryData')) {
                $helper = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'ComplexEnergyIntegral.lean') -Raw
                $sources.Add([regex]::Replace($helper, '(?m)^import[^\r\n]*(\r?\n|$)', ''))
                $oldIntegral = '  rw \[integral_add \(\(hi _ _\)\.ofReal.add[\s\S]*?' +
                    '  simp only \[integral_complex_ofReal\]'
                $source = $source -replace $oldIntegral,
                    ("  exact (LeanSolid.OpenAI372.integral_complex_energy`n" +
                     "    (hi Complex.reCLM Complex.reCLM) (hi Complex.imCLM Complex.imCLM)`n" +
                     "    (hi Complex.imCLM Complex.reCLM) (hi Complex.reCLM Complex.imCLM)).symm")
            }
        }
        'BoundaryJets' {
            $source = $source.Replace('| h n ih =>', '| ind n ih =>')
        }
        'Extension' {
            $source = $source.Replace('nlinarith [mul_pos hpos hpair]',
                "change 0 < 3 * f x + 2 * g x at hpair`n        nlinarith [mul_pos hpos hpair]")
        }
        'Transport' {
            $source = $source.Replace('(Metric.mem_closedBall.mp hz) (by linarith)',
                '(Metric.mem_closedBall.mp hz) (lt_add_of_pos_right r zero_lt_one)')
        }
    }
    $sources.Add("section`n-- $ModuleName`n$source`nend")
}

if ($ThroughModule) {
    Add-UpstreamModule "OAI.MathematicalPhysics.Elasticity.$ThroughModule"
    $suffix = $ThroughModule
} else {
    Add-UpstreamModule 'OAI.MathematicalPhysics.Elasticity.Variational'
    if (-not $BridgeOnly) {
        Add-UpstreamModule 'OAI.MathematicalPhysics.Elasticity.Uniqueness'
    }
    $adapterFiles = @('LeanSolidBridge.lean')
    if (-not $BridgeOnly) { $adapterFiles += 'LeanSolidUniqueness.lean' }
    foreach ($file in $adapterFiles) {
        $source = Get-Content -LiteralPath (Join-Path $PSScriptRoot $file) -Raw
        $body = [regex]::Replace($source, '(?m)^import[^\r\n]*(\r?\n|$)', '')
        $sources.Add("section`n$body`nend")
    }
    if ($BridgeOnly) {
        $sources.Add('#print axioms LeanSolid.Elastostatics.Sobolev.Domain.coefficients_equal_of_upstream_mainClaim')
    }
    $suffix = if ($BridgeOnly) { 'Bridge' } else { 'Uniqueness' }
}
$output = Join-Path $projectRoot ".lake/OpenAI372Check$suffix.lean"
$header = @('import Mathlib', 'import LeanSolid.Elastostatics.Sobolev.EuclideanEnergy',
    'set_option autoImplicit false', 'set_option maxHeartbeats 2000000',
    'set_option synthInstance.maxHeartbeats 100000')
Set-Content -LiteralPath $output -Value ($header + $sources.ToArray()) -Encoding utf8
if ($GenerateOnly) {
    Write-Output $output
    exit 0
}

$auditLog = [IO.Path]::ChangeExtension($output, '.log')
& lake -d $projectRoot env lean $output > $auditLog 2>&1
$leanStatus = $LASTEXITCODE
$leanOutput = Get-Content -LiteralPath $auditLog
$leanOutput | Write-Output
if ($leanStatus -ne 0) { exit $leanStatus }
if (-not $ThroughModule) {
    $name = if ($BridgeOnly) {
        'coefficients_equal_of_upstream_mainClaim'
    } else {
        'coefficients_equal_of_cartesian_DN_eq'
    }
    $audit = [regex]::Match(($leanOutput -join "`n"),
        [regex]::Escape("$name' depends on axioms:") + '\s*\[(?<axioms>[^\]]*)\]')
    $allowed = @('propext', 'Classical.choice', 'Quot.sound')
    $axioms = $audit.Groups['axioms'].Value -split ',\s*'
    if (-not $audit.Success -or ($axioms | Where-Object { $_.Trim() -notin $allowed })) {
        throw "Expected an audit of $name containing only Lean's standard axioms."
    }
}
exit 0
