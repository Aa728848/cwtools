Includes = { "gfx/FX/extension.fxh" }

PixelShader =
{
    MainCode Pixel
    [[
        float4 main(float2 uv) : PDX_COLOR { return ExtendedColor(uv); }
    ]]
}

Effect IncludeExtensionFixture
{
    PixelShader = "Pixel"
}
