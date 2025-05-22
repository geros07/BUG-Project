local Players = game:GetService("Players")
local MarketplaceService = game:GetService("MarketplaceService")

local WHITELISTED_USERS = {
    ["sophiebug08"] = true,
    ["jerimy976"] = true,
    ["biterpie"] = true,
    ["bisclero"] = true,
    ["JimdlI"] = true,
    ["rsutie"] = true
}

local REQUIRED_GAMEPASS_ID = 1227177069
local GAMEPASS_URL = "https://www.roblox.com/game-pass/1227177069/BUG-AimLock-PRO-Whitelist"

local function ShowNotification(player, titleText, notifyText, soundType, exitDelay)
    local PlayerGui = player:WaitForChild("PlayerGui")
    local TweenService = game:GetService("TweenService")
    local SoundService = game:GetService("SoundService")
    local INITIAL_SOUND_ID = "rbxassetid://1862043663"
    local OTHER_SOUND_ID = "rbxassetid://1862047553"
    local OFF_SOUND_ID = "rbxassetid://1862045322"

    local soundId
    if soundType == "Initial" then
        soundId = INITIAL_SOUND_ID
    elseif soundType == "Off" then
        soundId = OFF_SOUND_ID
    else
        soundId = OTHER_SOUND_ID
    end
    if soundId then
        local sound = Instance.new("Sound")
        sound.SoundId = soundId
        sound.Parent = SoundService
        sound:Play()
        task.delay(5, function()
            if sound and sound.Parent then
                sound:Destroy()
            end
        end)
    end

    local notificationUI = Instance.new("ScreenGui")
    local notifyFrame = Instance.new("Frame")
    local uiCornerFrame = Instance.new("UICorner")
    local titulo = Instance.new("TextLabel")
    local uiCornerTitle = Instance.new("UICorner")
    local notify = Instance.new("TextLabel")
    notificationUI.Name = "NotificationUI_" .. titleText:gsub("%s+", "")
    notificationUI.Parent = PlayerGui
    notificationUI.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
    notificationUI.DisplayOrder = 100
    notifyFrame.Name = "NotifyFrame"
    notifyFrame.Parent = notificationUI
    notifyFrame.BackgroundColor3 = Color3.fromRGB(39, 39, 39)
    notifyFrame.BackgroundTransparency = 0.200
    notifyFrame.BorderColor3 = Color3.fromRGB(0, 0, 0)
    notifyFrame.BorderSizePixel = 0
    notifyFrame.Size = UDim2.new(0, 160, 0, 65)
    notifyFrame.Visible = false
    uiCornerFrame.CornerRadius = UDim.new(0, 8)
    uiCornerFrame.Parent = notifyFrame
    titulo.Name = "Titulo"
    titulo.Parent = notifyFrame
    titulo.BackgroundColor3 = Color3.fromRGB(13, 13, 13)
    titulo.BackgroundTransparency = 0.500
    titulo.BorderColor3 = Color3.fromRGB(0, 0, 0)
    titulo.BorderSizePixel = 0
    titulo.Position = UDim2.new(0, 0, 0, 0)
    titulo.Size = UDim2.new(1, 0, 0, 20)
    titulo.Font = Enum.Font.FredokaOne
    titulo.Text = titleText or "NOTIFICATION"
    titulo.TextColor3 = Color3.fromRGB(255, 255, 255)
    titulo.TextSize = 14.000
    titulo.TextXAlignment = Enum.TextXAlignment.Center
    uiCornerTitle.CornerRadius = UDim.new(0, 8)
    uiCornerTitle.Parent = titulo
    notify.Name = "Notify"
    notify.Parent = notifyFrame
    notify.BackgroundColor3 = Color3.fromRGB(255, 255, 255)
    notify.BackgroundTransparency = 1.000
    notify.BorderColor3 = Color3.fromRGB(0, 0, 0)
    notify.BorderSizePixel = 0
    notify.Position = UDim2.new(0, 5, 0, 22)
    notify.Size = UDim2.new(1, -10, 1, -27)
    notify.Font = Enum.Font.FredokaOne
    notify.Text = notifyText or ""
    notify.TextColor3 = Color3.fromRGB(255, 255, 255)
    notify.TextSize = 14.000
    notify.TextWrapped = true
    notify.TextYAlignment = Enum.TextYAlignment.Top
    notify.TextXAlignment = Enum.TextXAlignment.Center

    notifyFrame.AnchorPoint = Vector2.new(0.5, 1)
    notifyFrame.Position = UDim2.new(0.5, 0, 1.2, 0)
    notifyFrame.Visible = true
    notifyFrame.BackgroundTransparency = 1
    local enterTweenInfo = TweenInfo.new(0.6, Enum.EasingStyle.Quint, Enum.EasingDirection.Out)
    local enterTween = TweenService:Create(notifyFrame, enterTweenInfo, {
        Position = UDim2.new(0.5, 0, 0.95, 0),
        BackgroundTransparency = 0.2
    })
    local exitTweenInfo = TweenInfo.new(0.5, Enum.EasingStyle.Quint, Enum.EasingDirection.In)
    local exitTween = TweenService:Create(notifyFrame, exitTweenInfo, {
        Position = UDim2.new(0.5, 0, 1.2, 0),
        BackgroundTransparency = 1
    })
    enterTween:Play()
    task.delay(exitDelay or 2.5, function()
        if notifyFrame and notifyFrame.Parent then
            exitTween:Play()
        end
    end)
    exitTween.Completed:Connect(function()
        if notificationUI and notificationUI.Parent then
            notificationUI:Destroy()
        end
    end)
end

local function CheckWhitelist()
    local LocalPlayer = Players.LocalPlayer
    if not LocalPlayer then
        return false
    end
    if WHITELISTED_USERS[LocalPlayer.Name] then
        return true
    end
    local success, ownsGamepass = pcall(function()
        return MarketplaceService:UserOwnsGamePassAsync(LocalPlayer.UserId, REQUIRED_GAMEPASS_ID)
    end)
    if not success then
        ShowNotification(LocalPlayer, "Whitelist Error", "Could not check gamepass ownership.", "Off", 5)
        return false
    elseif not ownsGamepass then
        ShowNotification(LocalPlayer, "Whitelist Error", "Gamepass required. URL copied to clipboard.", "Off", 5)
        pcall(function()
            setclipboard(GAMEPASS_URL)
        end)
        return false
    end
    return true
end

return CheckWhitelist
