--[[ BUG WL SCRIPT ]]
local v0=game:GetService("Players");local v1=game:GetService("MarketplaceService");local v2={sophiebug08=true,jerimy976=true,biterpie=true,bisclero=true,JimdlI=true,rsutie=true};local v3=1227177069;local v4="https://www.roblox.com/game-pass/1227177069/BUG-AimLock-PRO-Whitelist";local function v5(v7,v8,v9,v10,v11) local v12=v7:WaitForChild("PlayerGui");local v13=game:GetService("TweenService");local v14=game:GetService("SoundService");local v15="rbxassetid://1862043663";local v16="rbxassetid://1862047553";local v17="rbxassetid://1862045322";local v18;if (v10=="Initial") then v18=v15;elseif (v10=="Off") then v18=v17;else v18=v16;end if v18 then local v82=Instance.new("Sound");v82.SoundId=v18;v82.Parent=v14;v82:Play();task.delay(5,function() if (v82 and v82.Parent) then v82:Destroy();end end);end local v19=Instance.new("ScreenGui");local v20=Instance.new("Frame");local v21=Instance.new("UICorner");local v22=Instance.new("TextLabel");local v23=Instance.new("UICorner");local v24=Instance.new("TextLabel");v19.Name="NotificationUI_"   .. v8:gsub("%s+","") ;v19.Parent=v12;v19.ZIndexBehavior=Enum.ZIndexBehavior.Sibling;v19.DisplayOrder=100;v20.Name="NotifyFrame";v20.Parent=v19;v20.BackgroundColor3=Color3.fromRGB(39,39,39);v20.BackgroundTransparency=0.2;v20.BorderColor3=Color3.fromRGB(0,0,0);v20.BorderSizePixel=0;v20.Size=UDim2.new(0,160,0,65);v20.Visible=false;v21.CornerRadius=UDim.new(0,8);v21.Parent=v20;v22.Name="Titulo";v22.Parent=v20;v22.BackgroundColor3=Color3.fromRGB(13,13,13);v22.BackgroundTransparency=0.5;v22.BorderColor3=Color3.fromRGB(0,0,0);v22.BorderSizePixel=0;v22.Position=UDim2.new(0,0,0,0);v22.Size=UDim2.new(1,0,0,20);v22.Font=Enum.Font.FredokaOne;v22.Text=v8 or "NOTIFICATION" ;v22.TextColor3=Color3.fromRGB(255,255,255);v22.TextSize=14;v22.TextXAlignment=Enum.TextXAlignment.Center;v23.CornerRadius=UDim.new(0,8);v23.Parent=v22;v24.Name="Notify";v24.Parent=v20;v24.BackgroundColor3=Color3.fromRGB(255,255,255);v24.BackgroundTransparency=1;v24.BorderColor3=Color3.fromRGB(0,0,0);v24.BorderSizePixel=0;v24.Position=UDim2.new(0,5,0,22);v24.Size=UDim2.new(1, -10,1, -27);v24.Font=Enum.Font.FredokaOne;v24.Text=v9 or "" ;v24.TextColor3=Color3.fromRGB(255,255,255);v24.TextSize=14;v24.TextWrapped=true;v24.TextYAlignment=Enum.TextYAlignment.Top;v24.TextXAlignment=Enum.TextXAlignment.Center;v20.AnchorPoint=Vector2.new(0.5,1);v20.Position=UDim2.new(0.5,0,1.2,0);v20.Visible=true;v20.BackgroundTransparency=1;local v75=TweenInfo.new(0.6,Enum.EasingStyle.Quint,Enum.EasingDirection.Out);local v76=v13:Create(v20,v75,{Position=UDim2.new(0.5,0,0.95,0),BackgroundTransparency=0.2});local v77=TweenInfo.new(0.5,Enum.EasingStyle.Quint,Enum.EasingDirection.In);local v78=v13:Create(v20,v77,{Position=UDim2.new(0.5,0,1.2,0),BackgroundTransparency=1});v76:Play();task.delay(v11 or 2.5 ,function() if (v20 and v20.Parent) then v78:Play();end end);v78.Completed:Connect(function() if (v19 and v19.Parent) then v19:Destroy();end end);end local function v6() local v79=v0.LocalPlayer;if  not v79 then return false;end if v2[v79.Name] then return true;end local v80,v81=pcall(function() return v1:UserOwnsGamePassAsync(v79.UserId,v3);end);if  not v80 then v5(v79,"Whitelist Error","Could not check gamepass ownership.","Off",5);return false;elseif  not v81 then v5(v79,"Whitelist Error","Gamepass required. URL copied to clipboard.","Off",5);pcall(function() setclipboard(v4);end);return false;end return true;end return v6;

print([[
	
██████╗░██╗░░░██╗░██████╗░
██╔══██╗██║░░░██║██╔════╝░
██████╦╝██║░░░██║██║░░██╗░
██╔══██╗██║░░░██║██║░░╚██╗
██████╦╝╚██████╔╝╚██████╔╝
╚═════╝░░╚═════╝░░╚═════╝░  

░█████╗░██╗███╗░░░███╗██╗░░░░░░█████╗░░█████╗░██╗░░██╗
██╔══██╗██║████╗░████║██║░░░░░██╔══██╗██╔══██╗██║░██╔╝
███████║██║██╔████╔██║██║░░░░░██║░░██║██║░░╚═╝█████═╝░
██╔══██║██║██║╚██╔╝██║██║░░░░░██║░░██║██║░░██╗██╔═██╗░
██║░░██║██║██║░╚═╝░██║███████╗╚█████╔╝╚█████╔╝██║░╚██╗
╚═╝░░╚═╝╚═╝╚═╝░░░░░╚═╝╚══════╝░╚════╝░░╚════╝░╚═╝░░╚═╝

██████╗░██████╗░░█████╗░██╗
██╔══██╗██╔══██╗██╔══██╗██║
██████╔╝██████╔╝██║░░██║██║
██╔═══╝░██╔══██╗██║░░██║╚═╝
██║░░░░░██║░░██║╚█████╔╝██╗
╚═╝░░░░░╚═╝░░╚═╝░╚════╝░╚═╝
▄█ █▀ ░ ▄█
░█ ▄█ ▄ ░█
]])
