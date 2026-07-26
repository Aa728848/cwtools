Includes = { "gfx/FX/branch_a.fxh" "gfx/FX/branch_b.fxh" }
PixelShader = { MainCode Pixel [[ float4 main(float2 uv) : PDX_COLOR { return BranchA(uv) + BranchB(uv); } ]] }
Effect LargeGraphFixture { PixelShader = "Pixel" }
