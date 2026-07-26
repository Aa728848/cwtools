Includes = { "gfx/FX/common.fxh" "gfx/FX/leaf_a.fxh" }
float4 BranchA(float2 uv) { return Common(uv) + LeafA(uv); }
