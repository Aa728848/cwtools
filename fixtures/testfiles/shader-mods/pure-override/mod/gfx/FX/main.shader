Includes = { "gfx/FX/shared.fxh" }

PixelShader =
{
    MainCode Pixel
    [[
        float4 main(float2 uv) : PDX_COLOR { return ModOnly(uv); }
    ]]
}

Effect OverrideFixture
{
    PixelShader = "Pixel"
}
