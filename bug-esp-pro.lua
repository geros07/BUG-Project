local Players = game:GetService("Players")
local LocalPlayer = Players.LocalPlayer
local Workspace = game:GetService("Workspace")
local RunService = game:GetService("RunService")
local Camera = Workspace.CurrentCamera
local UserInputService = game:GetService("UserInputService")
local SoundService = game:GetService("SoundService")
local TweenService = game:GetService("TweenService")
local PlayerGui = LocalPlayer:WaitForChild("PlayerGui")

local Drawings = {}
local Highlights = {}
local currentNotificationGui = nil
local notificationEnabled = false

local ON_SOUND_ID = "rbxassetid://1862047553"
local OFF_SOUND_ID = "rbxassetid://1862045322"

local function PlayNotificationSound(soundType)
	local soundId
	if soundType == "Off" then
		soundId = OFF_SOUND_ID
	else
		soundId = ON_SOUND_ID
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
end

local function AnimateAndDestroy(notifyFrame, exitDelay)
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
	task.delay(exitDelay, function()
		if notifyFrame and notifyFrame.Parent then
			exitTween:Play()
		end
	end)
	exitTween.Completed:Connect(function()
		local guiToDestroy = notifyFrame and notifyFrame.Parent
		if guiToDestroy and guiToDestroy.Parent then
			if guiToDestroy == currentNotificationGui then
				currentNotificationGui = nil
			end
			guiToDestroy:Destroy()
		end
	end)
end

local function ShowNotification(titleText, notifyText, soundType, exitDelay)
	soundType = soundType or "Other"
	exitDelay = exitDelay or 2.5
	if currentNotificationGui and currentNotificationGui.Parent then
		currentNotificationGui:Destroy()
		currentNotificationGui = nil
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
	currentNotificationGui = notificationUI
	PlayNotificationSound(soundType)
	AnimateAndDestroy(notifyFrame, exitDelay)
end

local function GetTeamColor(player)
	if player.Team then
		return player.Team.TeamColor.Color
	end
	return nil
end

local function WorldToViewportPointPrecise(part)
	local minX, minY = math.huge, math.huge
	local maxX, maxY = -math.huge, -math.huge

	local cframe = part.CFrame
	local size = part.Size

	local corners = {
		cframe * CFrame.new(size.X/2, size.Y/2, size.Z/2),
		cframe * CFrame.new(-size.X/2, size.Y/2, size.Z/2),
		cframe * CFrame.new(size.X/2, -size.Y/2, size.Z/2),
		cframe * CFrame.new(-size.X/2, -size.Y/2, size.Z/2),
		cframe * CFrame.new(size.X/2, size.Y/2, -size.Z/2),
		cframe * CFrame.new(-size.X/2, size.Y/2, -size.Z/2),
		cframe * CFrame.new(size.X/2, -size.Y/2, -size.Z/2),
		cframe * CFrame.new(-size.X/2, -size.Y/2, -size.Z/2),
	}

	local onScreen = false
	for _, cornerCFrame in ipairs(corners) do
		local screenPoint, visible = Camera:WorldToViewportPoint(cornerCFrame.Position)
		if visible then
			onScreen = true
			minX = math.min(minX, screenPoint.X)
			minY = math.min(minY, screenPoint.Y)
			maxX = math.max(maxX, screenPoint.X)
			maxY = math.max(maxY, screenPoint.Y)
		end
	end

	if onScreen then
		return Vector2.new(minX, minY), Vector2.new(maxX, maxY), true
	else
		return Vector2.new(0, 0), Vector2.new(0, 0), false
	end
end

local function UpdateESP()
	for _, drawing in pairs(Drawings) do
		drawing:Remove()
	end
	Drawings = {}

	for _, highlight in pairs(Highlights) do
		highlight:Destroy()
	end
	Highlights = {}

	if notificationEnabled then
		for _, player in pairs(Players:GetPlayers()) do
			if player == LocalPlayer then continue end

			local character = player.Character
			if not character or not character:FindFirstChildOfClass("Humanoid") or character:FindFirstChildOfClass("Humanoid").Health <= 0 then
				continue
			end

			local rootPart = character:FindFirstChild("HumanoidRootPart")
			if not rootPart then continue end

			local topLeftScreen, bottomRightScreen, onScreen = WorldToViewportPointPrecise(rootPart)

			if onScreen then
				local boxColor = Color3.new(1, 1, 1)
				local highlightColor = Color3.new(1, 1, 1)

				local teamColor = GetTeamColor(player)
				if teamColor then
					boxColor = teamColor
					highlightColor = teamColor
				end

				local width = bottomRightScreen.X - topLeftScreen.X
				local height = bottomRightScreen.Y - topLeftScreen.Y

				local box = Drawing.new("Square")
				box.Position = topLeftScreen
				box.Size = Vector2.new(width, height)
				box.Color = boxColor
				box.Thickness = 2
				box.Filled = false
				table.insert(Drawings, box)

				local boxOutline = Drawing.new("Square")
				boxOutline.Position = topLeftScreen - Vector2.new(1, 1)
				boxOutline.Size = Vector2.new(width + 2, height + 2)
				boxOutline.Color = Color3.new(0, 0, 0)
				boxOutline.Thickness = 1
				boxOutline.Filled = false
				table.insert(Drawings, boxOutline)

				local healthPercentage = character:FindFirstChildOfClass("Humanoid").Health / character:FindFirstChildOfClass("Humanoid").MaxHealth
				local healthBarHeight = height * healthPercentage
				local healthBar = Drawing.new("Square")
				healthBar.Position = Vector2.new(bottomRightScreen.X + 5, topLeftScreen.Y)
				healthBar.Size = Vector2.new(5, healthBarHeight)
				healthBar.Color = Color3.new(1 - healthPercentage, healthPercentage, 0)
				healthBar.Thickness = 1
				healthBar.Filled = true
				table.insert(Drawings, healthBar)

				local healthBarOutline = Drawing.new("Square")
				healthBarOutline.Position = Vector2.new(bottomRightScreen.X + 4, topLeftScreen.Y - 1)
				healthBarOutline.Size = Vector2.new(7, height + 2)
				healthBarOutline.Color = Color3.new(0, 0, 0)
				healthBarOutline.Thickness = 1
				healthBarOutline.Filled = false
				table.insert(Drawings, healthBarOutline)

				local highlight = Instance.new("Highlight")
				highlight.Adornee = character
				highlight.FillTransparency = 0.5
				highlight.OutlineTransparency = 0
				highlight.OutlineColor = Color3.new(1, 1, 1)
				highlight.FillColor = highlightColor
				highlight.Parent = Workspace
				table.insert(Highlights, highlight)
			end
		end
	end
end

UserInputService.InputBegan:Connect(function(input, gameProcessedEvent)
	if gameProcessedEvent then return end

	if input.KeyCode == Enum.KeyCode.P and UserInputService:IsKeyDown(Enum.KeyCode.LeftShift) then
		notificationEnabled = not notificationEnabled
		if notificationEnabled then
			ShowNotification("ESP", "ESP ON", "On", 2.5)
		else
			ShowNotification("ESP", "ESP OFF", "Off", 2.5)
		end
	end
end)

RunService.RenderStepped:Connect(UpdateESP)
