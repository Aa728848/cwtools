Includes = { "gfx/FX/common.fxh" "gfx/FX/leaf_b.fxh" }
float4 BranchB(float2 uv) { return Common(uv) + LeafB(uv); }
