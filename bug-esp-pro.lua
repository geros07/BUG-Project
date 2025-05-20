local Players = game:GetService("Players")
local LocalPlayer = Players.LocalPlayer
local Workspace = game:GetService("Workspace")
local RunService = game:GetService("RunService")
local Camera = Workspace.CurrentCamera

local Drawings = {}
local Highlights = {}

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

RunService.RenderStepped:Connect(UpdateESP)