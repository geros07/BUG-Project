--[[

LEGIT BUG AIMLOCK PRO V.14

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 55) then
					if (Enum <= 27) then
						if (Enum <= 13) then
							if (Enum <= 6) then
								if (Enum <= 2) then
									if (Enum <= 0) then
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 1) then
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local B;
										local T;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum <= 4) then
									if (Enum == 3) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
									end
								elseif (Enum > 5) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 9) then
								if (Enum <= 7) then
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								elseif (Enum > 8) then
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local Edx;
									local Results;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 11) then
								if (Enum > 10) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum > 12) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 20) then
							if (Enum <= 16) then
								if (Enum <= 14) then
									Stk[Inst[2]] = {};
								elseif (Enum > 15) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 18) then
								if (Enum == 17) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 19) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							else
								do
									return;
								end
							end
						elseif (Enum <= 23) then
							if (Enum <= 21) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Enum == 22) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 25) then
							if (Enum == 24) then
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum == 26) then
							if (Stk[Inst[2]] > Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = VIP + Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 41) then
						if (Enum <= 34) then
							if (Enum <= 30) then
								if (Enum <= 28) then
									Stk[Inst[2]] = #Stk[Inst[3]];
								elseif (Enum > 29) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 32) then
								if (Enum == 31) then
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								end
							elseif (Enum > 33) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 37) then
							if (Enum <= 35) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 36) then
								local Edx;
								local Results;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 39) then
							if (Enum > 38) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] > Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = VIP + Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 40) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 48) then
						if (Enum <= 44) then
							if (Enum <= 42) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Enum == 43) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 46) then
							if (Enum == 45) then
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 47) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local Edx;
							local Results;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 51) then
						if (Enum <= 49) then
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						elseif (Enum > 50) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 53) then
						if (Enum > 52) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum == 54) then
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 83) then
					if (Enum <= 69) then
						if (Enum <= 62) then
							if (Enum <= 58) then
								if (Enum <= 56) then
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								elseif (Enum == 57) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 60) then
								if (Enum > 59) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 61) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 65) then
							if (Enum <= 63) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum == 64) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 67) then
							if (Enum > 66) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum == 68) then
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 76) then
						if (Enum <= 72) then
							if (Enum <= 70) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum > 71) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 74) then
							if (Enum == 73) then
								VIP = Inst[3];
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 75) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum <= 79) then
						if (Enum <= 77) then
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						elseif (Enum > 78) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 81) then
						if (Enum > 80) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum == 82) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 97) then
					if (Enum <= 90) then
						if (Enum <= 86) then
							if (Enum <= 84) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Enum == 85) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Stk[Inst[2]]();
							end
						elseif (Enum <= 88) then
							if (Enum > 87) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							end
						elseif (Enum > 89) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 93) then
						if (Enum <= 91) then
							local B;
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						elseif (Enum == 92) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 95) then
						if (Enum == 94) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						else
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum == 96) then
						if (Stk[Inst[2]] <= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Inst[3] do
							Insert(T, Stk[Idx]);
						end
					end
				elseif (Enum <= 104) then
					if (Enum <= 100) then
						if (Enum <= 98) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 99) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 102) then
						if (Enum > 101) then
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							Stk[Inst[2]] = not Stk[Inst[3]];
						end
					elseif (Enum == 103) then
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = #Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					else
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 23) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 108) then
					if (Enum <= 106) then
						if (Enum == 105) then
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = not Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum == 107) then
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						Upvalues[Inst[3]] = Stk[Inst[2]];
					end
				elseif (Enum <= 110) then
					if (Enum == 109) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = not Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum == 111) then
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
				elseif (Stk[Inst[2]] ~= Inst[4]) then
					VIP = VIP + 1;
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!4B3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030A3Q0052756E5365727669636503103Q0055736572496E7075745365727669636503093Q00576F726B7370616365030C3Q0054772Q656E53657276696365030C3Q00536F756E645365727669636503123Q004D61726B6574706C61636553657276696365030B3Q004C6F63616C506C61796572030B3Q00506C61796572412Q64656403043Q0057616974030C3Q0057616974466F724368696C6403093Q00506C6179657247756903083Q004765744D6F757365030D3Q0043752Q72656E7443616D657261030B3Q00736F7068696562756730382Q0103093Q006A6572696D7939373603083Q00626974657270696503063Q004A696D646C4903063Q0072737574696502008B04BC7669DA4203043Q00456E756D03073Q004B6579436F646503013Q0051030D3Q0055736572496E70757454797065030C3Q004D6F75736542752Q746F6E3103063Q00496E7365727403063Q0050616765557003083Q0050616765446F776E03013Q004503043Q00486F6D6503023Q00463203013Q005003063Q0044656C657465025Q00C07240025Q00805640025Q00805140027Q004003043Q004865616403053Q00546F72736F025Q00409F4003173Q00726278612Q73657469643A2Q2F313836323034332Q363303173Q00726278612Q73657469643A2Q2F313836323034372Q353303173Q00726278612Q73657469643A2Q2F31383632303435332Q3203063Q00436F6C6F723303073Q0066726F6D524742026Q004740025Q00206C40026Q00F03F03073Q00436F2Q6E656374030E3Q00506C6179657252656D6F76696E67030A3Q00476574506C6179657273030E3Q00436861726163746572412Q64656403183Q0047657450726F70657274794368616E6765645369676E616C03043Q005465616D03093Q00436861726163746572030A3Q00496E707574426567616E030A3Q00496E707574456E646564030D3Q0052656E6465725374652Q70656403113Q0043686172616374657252656D6F76696E67030B3Q004669656C644F6656696577030B3Q00446973706C61794E616D6503043Q004E616D6503063Q00747970656F6603063Q00737472696E67034Q0003063Q00506C6179657203073Q00556E6B6E6F776E03063Q00666F726D617403103Q0057656C636F6D6521202573284025732903143Q00284255472041696D4C6F636B2053797374656D2903073Q00496E697469616C026Q0012400061012Q0012183Q00013Q00206Q000200122Q000200038Q0002000200122Q000100013Q00202Q00010001000200122Q000300046Q00010003000200122Q000200013Q00202Q00020002000200120A000400054Q005B00020004000200122Q000300013Q00202Q00030003000200122Q000500066Q00030005000200122Q000400013Q00202Q00040004000200122Q000600076Q00040006000200122Q000500013Q00203200050005000200121B000700086Q00050007000200122Q000600013Q00202Q00060006000200122Q000800096Q00060008000200202Q00073Q000A00062Q00070023000100010004493Q0023000100204500083Q000B00203200080008000C2Q001000080002000100204500073Q000A00203200080007000D001215000A000E6Q0008000A000200202Q00090007000F4Q00090002000200202Q000A000300104Q000B3Q000500302Q000B0011001200302Q000B0013001200302Q000B0014001200302Q000B0015001200303E000B00160012001238000C00173Q00122Q000D00183Q00202Q000D000D001900202Q000D000D001A00122Q000E00183Q00202Q000E000E001B00202Q000E000E001C00122Q000F00183Q00202Q000F000F001900202Q000F000F001D001235001000183Q00205400100010001900202Q00100010001E00122Q001100183Q00202Q00110011001900202Q00110011001F00122Q001200183Q00202Q00120012001900202Q00120012002000122Q001300183Q00202Q001300130019002045001300130021001269001400183Q00202Q00140014001900202Q00140014002200122Q001500183Q00202Q00150015001900202Q00150015002300122Q001600183Q00202Q00160016001900202Q00160016002400122Q001700253Q00120A001800263Q001201001900273Q00122Q001A00286Q001B00023Q00122Q001C00293Q00122Q001D002A6Q001B0002000100120A001C002B3Q001229001D002C3Q00122Q001E002D3Q00122Q001F002E3Q00122Q0020002F3Q00202Q00200020003000122Q002100313Q00122Q002200323Q00122Q002300316Q0020002300024Q00216Q005C00226Q003600238Q002400016Q002500256Q002600186Q002700273Q00122Q002800336Q0029001B00284Q002A8Q002B5Q000668002C3Q000100042Q00173Q001D4Q00173Q001F4Q00173Q001E4Q00173Q00053Q000668002D0001000100022Q00173Q00044Q00173Q00273Q000668002E0002000100042Q00173Q00274Q00173Q00084Q00173Q002C4Q00173Q002D3Q000668002F0003000100052Q00173Q00074Q00173Q000B4Q00173Q00064Q00173Q000C4Q00173Q002E4Q00170030002F4Q006D00300001000200061200300083000100010004493Q008300012Q00133Q00013Q000204003000043Q00066800310005000100082Q00173Q00174Q00173Q00074Q00173Q000A4Q00173Q00094Q00178Q00173Q00304Q00173Q00294Q00173Q00243Q00066800320006000100022Q00173Q00224Q00173Q00253Q00066800330007000100012Q00173Q00203Q00066800340008000100022Q00173Q00074Q00173Q00333Q00066800350009000100012Q00173Q00073Q0006680036000A000100022Q00173Q00074Q00173Q00203Q0006680037000B000100012Q00173Q00073Q0006680038000C000100062Q00173Q002A4Q00173Q002E4Q00178Q00173Q00074Q00173Q00344Q00173Q00353Q0006680039000D000100062Q00173Q002B4Q00173Q002E4Q00178Q00173Q00074Q00173Q00364Q00173Q00373Q000668003A000E0001000B2Q00173Q00074Q00178Q00173Q00354Q00173Q00374Q00173Q001C4Q00173Q002A4Q00173Q00344Q00173Q00334Q00173Q002B4Q00173Q00364Q00173Q00203Q002045003B3Q000B002032003B003B0034000668003D000F000100042Q00173Q002A4Q00173Q00344Q00173Q002B4Q00173Q00364Q0005003B003D0001002045003B3Q0035002032003B003B0034000668003D0010000100022Q00173Q00354Q00173Q00374Q0005003B003D0001002032003B3Q00362Q002B003B0002003D0004493Q00EB000100062Q003F00EA000100070004493Q00EA00010020450040003F003700203200400040003400066800420011000100052Q00173Q002A4Q00173Q00344Q00173Q003F4Q00173Q002B4Q00173Q00364Q000D00400042000100202Q0040003F003800122Q004200396Q00400042000200202Q00400040003400066800420012000100052Q00173Q003F4Q00173Q002A4Q00173Q00344Q00173Q002B4Q00173Q00364Q00050040004200010020450040003F003A000652004000EA00013Q0004493Q00EA0001000652002A00E500013Q0004493Q00E500012Q0017004000344Q00170041003F4Q0010004000020001000652002B00EA00013Q0004493Q00EA00012Q0017004000364Q00170041003F4Q00100040000200012Q0057003E5Q000607003B00C7000100020004493Q00C70001002045003B0002003B002032003B003B0034000668003D00130001001E2Q00173Q000D4Q00173Q00024Q00173Q00214Q00173Q002E4Q00173Q00324Q00173Q00234Q00173Q000A4Q00173Q00184Q00173Q00264Q00173Q002A4Q00173Q00384Q00173Q000E4Q00173Q00254Q00173Q00314Q00173Q00224Q00173Q00104Q00173Q00114Q00173Q00194Q00173Q000F4Q00173Q00244Q00173Q00074Q00173Q00124Q00173Q00134Q00173Q00284Q00173Q001B4Q00173Q00294Q00173Q00144Q00173Q00154Q00173Q00164Q00173Q00394Q0005003B003D0001002045003B0002003C002032003B003B0034000668003D0014000100032Q00173Q000E4Q00173Q00234Q00173Q00324Q0005003B003D0001002045003B0001003D002032003B003B0034000668003D00150001000D2Q00173Q00214Q00173Q00224Q00173Q00234Q00173Q00094Q00173Q000A4Q00173Q00254Q00173Q00304Q00173Q00294Q00173Q00244Q00173Q00074Q00173Q00324Q00173Q001A4Q00173Q003A4Q0005003B003D0001002045003B00070037002032003B003B0034000668003D0016000100042Q00173Q00324Q00173Q00234Q00173Q000A4Q00173Q00264Q0005003B003D0001002045003B0007003E002032003B003B0034000668003D0017000100022Q00173Q00324Q00173Q00234Q000D003B003D000100202Q003B0007003800122Q003D00396Q003B003D000200202Q003B003B0034000668003D0018000100032Q00173Q00074Q00173Q002A4Q00173Q002B4Q0005003B003D0001000652000A00412Q013Q0004493Q00412Q0100106F000A003F0026000612000700442Q0100010004493Q00442Q012Q00133Q00013Q002045003B00070040002043003C0007004100122Q003D00426Q003E003B6Q003D0002000200262Q003D004D2Q0100430004493Q004D2Q01002651003B004E2Q0100440004493Q004E2Q0100120A003B00453Q001235003D00424Q0017003E003C4Q004C003D00020002002670003D00542Q0100430004493Q00542Q0100120A003C00463Q001235003D00433Q002053003D003D004700122Q003E00486Q003F003B6Q0040003C6Q003D004000024Q003E002E3Q00122Q003F00496Q0040003D3Q00122Q0041004A3Q00122Q0042004B4Q0005003E004200012Q00133Q00013Q00193Q000B3Q0003073Q00496E697469616C2Q033Q004F2Q6603083Q00496E7374616E63652Q033Q006E657703053Q00536F756E6403073Q00536F756E64496403063Q00506172656E7403043Q00506C617903043Q007461736B03053Q0064656C6179026Q001440011C3Q0026513Q0004000100010004493Q000400012Q002A00015Q0004493Q000900010026513Q0008000100020004493Q000800012Q002A000100013Q0004493Q000900012Q002A000100023Q0006520001001B00013Q0004493Q001B0001001235000200033Q00204D00020002000400122Q000300056Q00020002000200102Q0002000600014Q000300033Q00102Q00020007000300202Q0003000200084Q00030002000100122Q000300093Q00202Q00030003000A00122Q0004000B3Q00066800053Q000100012Q00173Q00024Q00050003000500012Q005700026Q00133Q00013Q00013Q00023Q0003063Q00506172656E7403073Q0044657374726F79000B4Q002A7Q0006523Q000A00013Q0004493Q000A00012Q002A7Q0020455Q00010006523Q000A00013Q0004493Q000A00012Q002A7Q0020325Q00022Q00103Q000200012Q00133Q00017Q001C3Q00030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577026Q00E03F026Q00F03F03083Q00506F736974696F6E03053Q005544696D32028Q00026Q33F33F03073Q0056697369626C652Q0103163Q004261636B67726F756E645472616E73706172656E637903093Q0054772Q656E496E666F026Q33E33F03043Q00456E756D030B3Q00456173696E675374796C6503053Q005175696E74030F3Q00456173696E67446972656374696F6E2Q033Q004F757403063Q00437265617465026Q66EE3F029A5Q99C93F03023Q00496E03043Q00506C617903043Q007461736B03053Q0064656C617903093Q00436F6D706C6574656403073Q00436F2Q6E65637402523Q00125D000200023Q00202Q00020002000300122Q000300043Q00122Q000400056Q00020004000200104Q0001000200122Q000200073Q00202Q00020002000300122Q000300043Q00122Q000400083Q00122Q000500093Q00122Q000600086Q00020006000200104Q0006000200304Q000A000B00304Q000C000500122Q0002000D3Q00202Q00020002000300122Q0003000E3Q00122Q0004000F3Q00202Q00040004001000202Q00040004001100122Q0005000F3Q00202Q00050005001200202Q0005000500134Q0002000500024Q00035Q00202Q0003000300144Q00058Q000600026Q00073Q000200122Q000800073Q00202Q00080008000300122Q000900043Q00122Q000A00083Q00122Q000B00153Q00122Q000C00086Q0008000C000200102Q00070006000800302Q0007000C00164Q00030007000200122Q0004000D3Q00202Q00040004000300122Q000500043Q00122Q0006000F3Q00202Q00060006001000202Q00060006001100122Q0007000F3Q00202Q00070007001200202Q0007000700174Q0004000700024Q00055Q00202Q0005000500144Q00078Q000800046Q00093Q000200122Q000A00073Q00202Q000A000A000300122Q000B00043Q00122Q000C00083Q00122Q000D00093Q00122Q000E00086Q000A000E000200102Q00090006000A00302Q0009000C00054Q00050009000200202Q0006000300184Q00060002000100122Q000600193Q00202Q00060006001A4Q000700013Q00066800083Q000100022Q00178Q00173Q00054Q000500060008000100204500060005001B00203200060006001C00066800080001000100022Q00178Q002A3Q00014Q00050006000800012Q00133Q00013Q00023Q00023Q0003063Q00506172656E7403043Q00506C6179000B4Q002A7Q0006523Q000A00013Q0004493Q000A00012Q002A7Q0020455Q00010006523Q000A00013Q0004493Q000A00012Q002A3Q00013Q0020325Q00022Q00103Q000200012Q00133Q00017Q00023Q0003063Q00506172656E7403073Q0044657374726F7900124Q002A7Q0006523Q000500013Q0004493Q000500012Q002A7Q0020455Q00010006523Q001100013Q0004493Q0011000100204500013Q00010006520001001100013Q0004493Q001100012Q002A000100013Q0006233Q000F000100010004493Q000F00012Q0040000100014Q006C000100013Q00203200013Q00022Q00100001000200012Q00133Q00017Q00403Q0003053Q004F74686572026Q00044003063Q00506172656E7403073Q0044657374726F7903083Q00496E7374616E63652Q033Q006E657703093Q005363722Q656E47756903053Q004672616D6503083Q005549436F726E657203093Q00546578744C6162656C03043Q004E616D65030F3Q004E6F74696669636174696F6E55495F03043Q00677375622Q033Q0025732B034Q00030E3Q005A496E6465784265686176696F7203043Q00456E756D03073Q005369626C696E67030C3Q00446973706C61794F72646572026Q005940030B3Q004E6F746966794672616D6503103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742025Q0080434003163Q004261636B67726F756E645472616E73706172656E6379029A5Q99C93F030C3Q00426F72646572436F6C6F7233028Q00030F3Q00426F7264657253697A65506978656C03043Q0053697A6503053Q005544696D32026Q006440025Q0040504003073Q0056697369626C650100030C3Q00436F726E657252616469757303043Q005544696D026Q00204003063Q00546974756C6F026Q002A40026Q00E03F03083Q00506F736974696F6E026Q00F03F026Q00344003043Q00466F6E74030A3Q00467265646F6B614F6E6503043Q0054657874030C3Q004E4F54494649434154494F4E030A3Q0054657874436F6C6F7233025Q00E06F4003083Q005465787453697A65026Q002C40030E3Q005465787458416C69676E6D656E7403063Q0043656E74657203063Q004E6F74696679026Q001440026Q003640026Q0024C0026Q003BC0030B3Q00546578745772612Q7065642Q01030E3Q005465787459416C69676E6D656E742Q033Q00546F7004DB3Q00061200020003000100010004493Q0003000100120A000200013Q00061200030006000100010004493Q0006000100120A000300024Q002A00045Q0006520004001200013Q0004493Q001200012Q002A00045Q0020450004000400030006520004001200013Q0004493Q001200012Q002A00045Q0020320004000400042Q00100004000200012Q0040000400044Q006C00045Q001235000400053Q00204400040004000600122Q000500076Q00040002000200122Q000500053Q00202Q00050005000600122Q000600086Q00050002000200122Q000600053Q00202Q00060006000600122Q000700096Q00060002000200122Q000700053Q00202Q00070007000600122Q0008000A6Q00070002000200122Q000800053Q00202Q00080008000600122Q000900096Q00080002000200122Q000900053Q00202Q00090009000600122Q000A000A6Q00090002000200122Q000A000C3Q00202Q000B3Q000D00122Q000D000E3Q00122Q000E000F6Q000B000E00024Q000A000A000B00102Q0004000B000A4Q000A00013Q00102Q00040003000A00122Q000A00113Q00202Q000A000A001000202Q000A000A001200102Q00040010000A00302Q00040013001400302Q0005000B001500102Q00050003000400122Q000A00173Q00202Q000A000A001800122Q000B00193Q00122Q000C00193Q00122Q000D00196Q000A000D000200102Q00050016000A00302Q0005001A001B00122Q000A00173Q00202Q000A000A001800122Q000B001D3Q00122Q000C001D3Q00122Q000D001D6Q000A000D000200102Q0005001C000A00302Q0005001E001D00122Q000A00203Q00202Q000A000A000600122Q000B001D3Q00122Q000C00213Q00122Q000D001D3Q00122Q000E00226Q000A000E000200102Q0005001F000A00302Q00050023002400122Q000A00263Q00202Q000A000A000600122Q000B001D3Q00122Q000C00276Q000A000C000200102Q00060025000A00102Q00060003000500302Q0007000B002800102Q00070003000500122Q000A00173Q00202Q000A000A001800122Q000B00293Q00122Q000C00293Q00122Q000D00296Q000A000D000200102Q00070016000A00303E0007001A002A001247000A00173Q00202Q000A000A001800122Q000B001D3Q00122Q000C001D3Q00122Q000D001D6Q000A000D000200102Q0007001C000A00302Q0007001E001D00122Q000A00203Q00202Q000A000A000600122Q000B001D3Q00122Q000C001D3Q00122Q000D001D3Q00122Q000E001D6Q000A000E000200102Q0007002B000A00122Q000A00203Q00202Q000A000A000600122Q000B002C3Q00122Q000C001D3Q00122Q000D001D3Q00122Q000E002D6Q000A000E000200102Q0007001F000A00122Q000A00113Q00202Q000A000A002E00202Q000A000A002F00102Q0007002E000A00062Q000A008300013Q0004493Q0083000100120A000A00313Q00106F00070030000A001234000A00173Q00202Q000A000A001800122Q000B00333Q00122Q000C00333Q00122Q000D00336Q000A000D000200102Q00070032000A00302Q00070034003500122Q000A00113Q00202Q000A000A003600202Q000A000A003700102Q00070036000A00122Q000A00263Q00202Q000A000A000600122Q000B001D3Q00122Q000C00276Q000A000C000200102Q00080025000A00102Q00080003000700302Q0009000B003800102Q00090003000500122Q000A00173Q00202Q000A000A001800122Q000B00333Q00122Q000C00333Q00122Q000D00336Q000A000D000200102Q00090016000A00302Q0009001A002C00122Q000A00173Q00202Q000A000A001800122Q000B001D3Q00122Q000C001D3Q00122Q000D001D6Q000A000D000200102Q0009001C000A00302Q0009001E001D00122Q000A00203Q00202Q000A000A000600122Q000B001D3Q00122Q000C00393Q00122Q000D001D3Q00122Q000E003A6Q000A000E000200102Q0009002B000A00122Q000A00203Q00202Q000A000A000600122Q000B002C3Q00122Q000C003B3Q00122Q000D002C3Q00122Q000E003C6Q000A000E000200102Q0009001F000A00122Q000A00113Q00202Q000A000A002E00202Q000A000A002F00102Q0009002E000A00062Q000A00C0000100010004493Q00C0000100120A000A000F3Q00106F00090030000A001264000A00173Q00202Q000A000A001800122Q000B00333Q00122Q000C00333Q00122Q000D00336Q000A000D000200102Q00090032000A00302Q00090034003500302Q0009003D003E00122Q000A00113Q00202Q000A000A003F00202Q000A000A004000102Q0009003F000A00122Q000A00113Q00202Q000A000A003600202Q000A000A003700102Q00090036000A4Q00048Q000A00026Q000B00026Q000A000200014Q000A00036Q000B00056Q000C00036Q000A000C00016Q00017Q00073Q0003043Q004E616D6503053Q007063612Q6C030F3Q0057686974656C69737420452Q726F72031A3Q00436F756C64206E6F7420636865636B206F776E6572736869702E2Q033Q004F2Q66026Q00144003253Q00596F7520646F206E6F7420686176652074686520726571756972656420542D73686972742E002B4Q002A7Q0006123Q0005000100010004493Q000500012Q005C8Q004E3Q00024Q002A3Q00014Q002A00015Q0020450001000100012Q00225Q00010006523Q000D00013Q0004493Q000D00012Q005C3Q00014Q004E3Q00023Q0012353Q00023Q00066800013Q000100032Q002A3Q00024Q002A8Q002A3Q00034Q002B3Q000200010006123Q001E000100010004493Q001E00012Q002A000200043Q001233000300033Q00122Q000400043Q00122Q000500053Q00122Q000600066Q0002000600014Q00028Q000200023Q0004493Q0028000100061200010028000100010004493Q002800012Q002A000200043Q001233000300033Q00122Q000400073Q00122Q000500053Q00122Q000600066Q0002000600014Q00028Q000200024Q005C000200014Q004E000200024Q00133Q00013Q00013Q00013Q00030F3Q00506C617965724F776E73412Q73657400074Q00557Q00206Q00014Q000200016Q000300028Q00039Q008Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403053Q00546F72736F030A3Q00552Q706572546F72736F02113Q0006123Q0004000100010004493Q000400012Q0040000200024Q004E000200023Q00203200023Q00012Q0017000400014Q00370002000400020006120002000F000100010004493Q000F00010026510001000F000100020004493Q000F000100203200033Q000100120A000500034Q00370003000500022Q0017000200034Q004E000200024Q00133Q00017Q000D3Q0003093Q0043686172616374657203073Q00566563746F72322Q033Q006E657703013Q005803013Q0059030A3Q00476574506C617965727303153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q004865616C7468028Q0003043Q005465616D03053Q007063612Q6C03093Q004D61676E697475646500534Q002A00016Q002A000200013Q0006520002000E00013Q0004493Q000E00012Q002A000200013Q0020450002000200010006520002000E00013Q0004493Q000E00012Q002A000200023Q0006520002000E00013Q0004493Q000E00012Q002A000200033Q00061200020010000100010004493Q001000012Q0040000200024Q004E000200023Q001235000200023Q0020250002000200034Q000300033Q00202Q0003000300044Q000400033Q00202Q0004000400054Q0002000400024Q000300043Q00202Q0003000300064Q00030002000500044Q004F00012Q002A000800013Q00062Q0007004F000100080004493Q004F00010020450008000700010006520008004F00013Q0004493Q004F00012Q002A000800053Q00205F0009000700014Q000A00066Q0008000A000200202Q00090007000100202Q00090009000700122Q000B00086Q0009000B000200062Q0008004F00013Q0004493Q004F00010006520009004F00013Q0004493Q004F0001002045000A00090009002660000A00310001000A0004493Q003100010004493Q004F00012Q002A000A00073Q000652000A003A00013Q0004493Q003A0001002045000A0007000B2Q002A000B00013Q002045000B000B000B000623000A003A0001000B0004493Q003A00010004493Q004F0001001235000A000C3Q000668000B3Q000100022Q002A3Q00024Q00173Q00084Q002B000A0002000C000652000A004E00013Q0004493Q004E0001000652000C004E00013Q0004493Q004E0001001235000D00023Q00203D000D000D000300202Q000E000B000400202Q000F000B00054Q000D000F00024Q000E000D000200202Q000E000E000D00062Q000E004E000100010004493Q004E00012Q00173Q00074Q00170001000E4Q005700085Q0006070003001B000100020004493Q001B00012Q004E3Q00024Q00133Q00013Q00013Q00023Q0003123Q00576F726C64546F5363722Q656E506F696E7403083Q00506F736974696F6E00074Q00637Q00206Q00014Q000200013Q00202Q0002000200026Q00029Q008Q00019Q003Q00054Q00099Q009Q009Q003Q00018Q00017Q000D3Q0003093Q00436861726163746572030B3Q00446973706C61794E616D6503043Q004E616D6503063Q00506C6179657203043Q005465616D2Q033Q004E2F4103093Q005465616D436F6C6F7203053Q00436F6C6F72030A3Q0054657874436F6C6F723303043Q005465787403063Q00737472696E6703063Q00666F726D617403093Q002573202D205B25735D02273Q00204500020001000100061200020004000100010004493Q000400012Q00133Q00013Q0020450003000100020006120003000B000100010004493Q000B00010020450003000100030006120003000B000100010004493Q000B000100120A000300043Q0020450004000100050006520004001200013Q0004493Q0012000100204500040001000500204500040004000300061200040013000100010004493Q0013000100120A000400064Q002A00055Q0020450006000100050006520006001E00013Q0004493Q001E00010020450006000100050020450006000600070006520006001E00013Q0004493Q001E000100204500060001000500204500060006000700204500050006000800106F3Q000900050012620006000B3Q00202Q00060006000C00122Q0007000D6Q000800036Q000900046Q00060009000200104Q000A00066Q00017Q002C3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403043Q0048656164030B3Q004E616D657461675F45535003083Q00496E7374616E63652Q033Q006E6577030C3Q0042692Q6C626F61726447756903043Q004E616D6503073Q0041646F726E2Q6503043Q0053697A6503053Q005544696D32028Q00025Q00C06240026Q004940030B3Q0053747564734F2Q6673657403073Q00566563746F7233026Q00F83F030B3Q00416C776179734F6E546F702Q0103063Q00506172656E7403093Q00546578744C6162656C03103Q004E616D657461674C6162656C5F455350026Q00F03F03163Q004261636B67726F756E645472616E73706172656E637903103Q00546578745374726F6B65436F6C6F723303063Q00436F6C6F723303073Q0066726F6D52474203163Q00546578745374726F6B655472616E73706172656E637903043Q00466F6E7403043Q00456E756D03043Q00436F6465030A3Q00546578745363616C6564010003083Q005465787453697A65026Q002F40030B3Q00546578745772612Q706564030E3Q005465787458416C69676E6D656E7403063Q0043656E746572030E3Q005465787459416C69676E6D656E7403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403043Q004469656403073Q00436F2Q6E65637403073Q00456E61626C656401664Q002A00015Q00064Q0006000100010004493Q0006000100204500013Q000100061200010007000100010004493Q000700012Q00133Q00013Q00204500013Q000100203200020001000200120A000400034Q00370002000400020006120002000E000100010004493Q000E00012Q00133Q00013Q00203200030002000200120A000500044Q00370003000500020006120003005B000100010004493Q005B0001001235000400053Q00201600040004000600122Q000500076Q0004000200024Q000300043Q00302Q00030008000400102Q00030009000200122Q0004000B3Q00202Q00040004000600122Q0005000C3Q00122Q0006000D3Q00122Q0007000C3Q00122Q0008000E6Q00040008000200102Q0003000A000400122Q000400103Q00202Q00040004000600122Q0005000C3Q00122Q000600113Q00122Q0007000C6Q00040007000200102Q0003000F000400302Q00030012001300102Q00030014000200122Q000400053Q00202Q00040004000600122Q000500156Q00040002000200302Q00040008001600122Q0005000B3Q00202Q00050005000600122Q000600173Q00122Q0007000C3Q00122Q000800173Q00122Q0009000C6Q00050009000200102Q0004000A000500302Q00040018001700122Q0005001A3Q00202Q00050005001B00122Q0006000C3Q00122Q0007000C3Q00122Q0008000C6Q00050008000200102Q00040019000500302Q0004001C000C00122Q0005001E3Q00202Q00050005001D00202Q00050005001F00102Q0004001D000500302Q00040020002100302Q00040022002300302Q00040024002100122Q0005001E3Q00202Q00050005002500202Q00050005002600102Q00040025000500122Q0005001E3Q00202Q00050005002700202Q00050005002600102Q00040027000500102Q00040014000300202Q00050001002800122Q000700296Q00050007000200062Q0005005B00013Q0004493Q005B000100204500060005002A00203200060006002B00066800083Q000100012Q00173Q00034Q000500060008000100303E0003002C001300203200040003000200120A000600164Q00370004000600020006520004006500013Q0004493Q006500012Q002A000500014Q0017000600044Q001700076Q00050005000700012Q00133Q00013Q00013Q00023Q0003063Q00506172656E7403073Q0044657374726F79000B4Q002A7Q0006523Q000A00013Q0004493Q000A00012Q002A7Q0020455Q00010006523Q000A00013Q0004493Q000A00012Q002A7Q0020325Q00022Q00103Q000200012Q00133Q00017Q00063Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403043Q0048656164030B3Q004E616D657461675F45535003073Q00456E61626C6564010001144Q002A00015Q00064Q0006000100010004493Q0006000100204500013Q000100061200010007000100010004493Q000700012Q00133Q00013Q00204500013Q000100203200010001000200120A000300034Q00370001000300020006520001001300013Q0004493Q0013000100203200020001000200120A000400044Q00370002000400020006520002001300013Q0004493Q0013000100303E0002000500062Q00133Q00017Q00163Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C64030D3Q004553505F486967686C6967687403083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403043Q004E616D6503063Q00506172656E7403043Q005465616D03093Q005465616D436F6C6F7203053Q00436F6C6F7203093Q0046692Q6C436F6C6F72030C3Q004F75746C696E65436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742028Q0003103Q0046692Q6C5472616E73706172656E6379026Q66E63F03133Q004F75746C696E655472616E73706172656E6379029A5Q99B93F03073Q00456E61626C65643Q012B4Q002A00015Q00064Q0006000100010004493Q0006000100204500013Q000100061200010007000100010004493Q000700012Q00133Q00013Q00204500013Q000100203200020001000200120A000400034Q003700020004000200061200020014000100010004493Q00140001001235000300043Q00202400030003000500122Q000400066Q0003000200024Q000200033Q00302Q00020007000300102Q0002000800012Q002A000300013Q00204500043Q00090006520004001F00013Q0004493Q001F000100204500043Q000900204500040004000A0006520004001F00013Q0004493Q001F000100204500043Q000900204500040004000A00204500030004000B00106F0002000C000300126B0004000E3Q00202Q00040004000F00122Q000500103Q00122Q000600103Q00122Q000700106Q00040007000200102Q0002000D000400302Q00020011001200302Q00020013001400302Q0002001500166Q00017Q00053Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C64030D3Q004553505F486967686C6967687403073Q00456E61626C6564010001114Q002A00015Q00064Q0006000100010004493Q0006000100204500013Q000100061200010007000100010004493Q000700012Q00133Q00013Q00204500013Q00010006520001001000013Q0004493Q0010000100203200020001000200120A000400034Q00370002000400020006520002001000013Q0004493Q0010000100303E0002000400052Q00133Q00017Q00073Q0003073Q00456E61626C656403083Q0044697361626C656403053Q004F746865722Q033Q004F2Q66030B3Q004E616D6574616720455350030A3Q00476574506C617965727303093Q00436861726163746572002D4Q006A9Q009Q009Q007Q00064Q000900013Q0004493Q0009000100120A3Q00013Q0006123Q000A000100010004493Q000A000100120A3Q00024Q002A00015Q0006520001001000013Q0004493Q0010000100120A000100033Q00061200010011000100010004493Q0011000100120A000100044Q002A000200013Q001208000300056Q00048Q000500016Q0002000500014Q000200023Q00202Q0002000200064Q00020002000400044Q002A00012Q002A000700033Q00062Q0006002A000100070004493Q002A00010020450007000600070006520007002A00013Q0004493Q002A00012Q002A00075Q0006520007002700013Q0004493Q002700012Q002A000700044Q0017000800064Q00100007000200010004493Q002A00012Q002A000700054Q0017000800064Q00100007000200010006070002001A000100020004493Q001A00012Q00133Q00017Q00073Q0003073Q00456E61626C656403083Q0044697361626C656403053Q004F746865722Q033Q004F2Q66030D3Q00486967686C6967687420455350030A3Q00476574506C617965727303093Q00436861726163746572002D4Q006A9Q009Q009Q007Q00064Q000900013Q0004493Q0009000100120A3Q00013Q0006123Q000A000100010004493Q000A000100120A3Q00024Q002A00015Q0006520001001000013Q0004493Q0010000100120A000100033Q00061200010011000100010004493Q0011000100120A000100044Q002A000200013Q001208000300056Q00048Q000500016Q0002000500014Q000200023Q00202Q0002000200064Q00020002000400044Q002A00012Q002A000700033Q00062Q0006002A000100070004493Q002A00010020450007000600070006520007002A00013Q0004493Q002A00012Q002A00075Q0006520007002700013Q0004493Q002700012Q002A000700044Q0017000800064Q00100007000200010004493Q002A00012Q002A000700054Q0017000800064Q00100007000200010006070002001A000100020004493Q001A00012Q00133Q00017Q00143Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403043Q0048656164030A3Q00476574506C617965727303153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q004865616C7468028Q00030B3Q004E616D657461675F45535003073Q00456E61626C6564030D3Q004553505F486967686C6967687403083Q00506F736974696F6E03093Q004D61676E697475646503103Q004E616D657461674C6162656C5F455350010003043Q005465616D03093Q005465616D436F6C6F7203053Q00436F6C6F7203093Q0046692Q6C436F6C6F722Q0100964Q002A7Q0006523Q000700013Q0004493Q000700012Q002A7Q0020455Q00010006123Q0008000100010004493Q000800012Q00133Q00014Q002A7Q00203C5Q000100206Q000200122Q000200038Q0002000200064Q0010000100010004493Q001000012Q00133Q00014Q002A000100013Q0020320001000100042Q002B0001000200030004493Q009300012Q002A00065Q00062Q00050093000100060004493Q009300010020450006000500010006520006009300013Q0004493Q0093000100204500060005000100200600070006000200122Q000900036Q00070009000200202Q00080006000500122Q000A00066Q0008000A000200062Q0007002800013Q0004493Q002800010006520008002800013Q0004493Q0028000100204500090008000700266000090041000100080004493Q004100010006420009002D000100070004493Q002D000100203200090007000200120A000B00094Q00370009000B00020006520009003500013Q0004493Q00350001002045000A0009000A000652000A003500013Q0004493Q003500012Q002A000A00024Q0017000B00054Q0010000A00020001002032000A0006000200120A000C000B4Q0037000A000C0002000652000A009300013Q0004493Q00930001002045000B000A000A000652000B009300013Q0004493Q009300012Q002A000B00034Q0017000C00054Q0010000B000200010004493Q0093000100204500090007000C002027000A3Q000C4Q00090009000A00202Q00090009000D4Q000A00043Q00062Q000900020001000A0004493Q004900012Q0050000A6Q005C000A00013Q002030000B0007000200122Q000D00096Q000B000D00024Q000C00053Q00062Q000C006800013Q0004493Q00680001000612000B0059000100010004493Q005900012Q002A000C00064Q0066000D00056Q000C0002000100202Q000C0007000200122Q000E00096Q000C000E00024Q000B000C3Q000652000B006E00013Q0004493Q006E000100106F000B000A000A000652000A006E00013Q0004493Q006E0001002032000C000B000200120A000E000E4Q0037000C000E0002000652000C006E00013Q0004493Q006E00012Q002A000D00074Q0017000E000C4Q0017000F00054Q0005000D000F00010004493Q006E0001000652000B006E00013Q0004493Q006E0001002045000C000B000A000652000C006E00013Q0004493Q006E000100303E000B000A000F002032000C0006000200120A000E000B4Q0037000C000E00022Q002A000D00083Q000652000D008D00013Q0004493Q008D0001000612000C007D000100010004493Q007D00012Q002A000D00094Q0066000E00056Q000D0002000100202Q000D0006000200122Q000F000B6Q000D000F00024Q000C000D3Q000652000C009300013Q0004493Q009300012Q002A000D000A3Q002045000E00050010000652000E008A00013Q0004493Q008A0001002045000E00050010002045000E000E0011000652000E008A00013Q0004493Q008A0001002045000E00050010002045000E000E0011002045000D000E001200106F000C0013000D00303E000C000A00140004493Q00930001000652000C009300013Q0004493Q00930001002045000D000C000A000652000D009300013Q0004493Q0093000100303E000C000A000F00060700010014000100020004493Q001400012Q00133Q00017Q00043Q00030E3Q00436861726163746572412Q64656403073Q00436F2Q6E65637403183Q0047657450726F70657274794368616E6765645369676E616C03043Q005465616D01153Q00204500013Q000100203200010001000200066800033Q000100052Q002A8Q002A3Q00014Q00178Q002A3Q00024Q002A3Q00034Q000D00010003000100202Q00013Q000300122Q000300046Q00010003000200202Q00010001000200066800030001000100052Q00178Q002A8Q002A3Q00014Q002A3Q00024Q002A3Q00034Q00050001000300012Q00133Q00013Q00027Q00010D4Q002A00015Q0006520001000600013Q0004493Q000600012Q002A000100014Q002A000200024Q00100001000200012Q002A000100033Q0006520001000C00013Q0004493Q000C00012Q002A000100044Q002A000200024Q00100001000200012Q00133Q00017Q00013Q0003093Q0043686172616374657200114Q002A7Q0020455Q00010006523Q001000013Q0004493Q001000012Q002A3Q00013Q0006523Q000A00013Q0004493Q000A00012Q002A3Q00024Q002A00016Q00103Q000200012Q002A3Q00033Q0006523Q001000013Q0004493Q001000012Q002A3Q00044Q002A00016Q00103Q000200012Q00133Q00019Q002Q0001074Q000200018Q00028Q0001000200014Q000100016Q00028Q0001000200016Q00019Q002Q00010D4Q002A00015Q0006520001000600013Q0004493Q000600012Q002A000100014Q002A000200024Q00100001000200012Q002A000100033Q0006520001000C00013Q0004493Q000C00012Q002A000100044Q002A000200024Q00100001000200012Q00133Q00017Q00013Q0003093Q0043686172616374657200114Q002A7Q0020455Q00010006523Q001000013Q0004493Q001000012Q002A3Q00013Q0006523Q000A00013Q0004493Q000A00012Q002A3Q00024Q002A00016Q00103Q000200012Q002A3Q00033Q0006523Q001000013Q0004493Q001000012Q002A3Q00044Q002A00016Q00103Q000200012Q00133Q00017Q001E3Q00030D3Q0055736572496E7075745479706503073Q004B6579436F646503093Q0049734B6579446F776E03043Q00456E756D03093Q004C6566745368696674030A3Q005269676874536869667403023Q00463103053Q004F746865722Q033Q004F2Q6603073Q0041696D4C6F636B03073Q00456E61626C656403083Q0044697361626C6564030B3Q004669656C644F6656696577002Q033Q00464F5603073Q0053657420746F2003083Q00746F737472696E67030A3Q005465616D20436865636B03023Q004F4E2Q033Q004F2Q4603043Q005465616D026Q00F03F030A3Q0041696D20546172676574030C3Q004D6F75736542752Q746F6E31030C3Q004D6F75736542752Q746F6E32030A3Q0041696D2042752Q746F6E03123Q0053657420746F205269676874204D6F75736503113Q0053657420746F204C656674204D6F757365030B3Q004E616D657461672045535003173Q0041696D4C6F636B206D75737420626520456E61626C65640230012Q0006520001000300013Q0004493Q000300012Q00133Q00013Q00204500023Q000100204500033Q00022Q002A00045Q00062300030018000100040004493Q001800012Q002A000400013Q00204A00040004000300122Q000600043Q00202Q00060006000200202Q0006000600054Q00040006000200062Q0004001D000100010004493Q001D00012Q002A000400013Q00204A00040004000300122Q000600043Q00202Q00060006000200202Q0006000600064Q00040006000200062Q0004001D000100010004493Q001D0001001235000400043Q0020450004000400020020450004000400070006230003004E000100040004493Q004E00012Q002A000400024Q0065000400044Q006C000400024Q002A000400023Q0006520004002600013Q0004493Q0026000100120A000400083Q00061200040027000100010004493Q0027000100120A000400094Q002A000500033Q00120A0006000A4Q002A000700023Q0006520007002F00013Q0004493Q002F000100120A0007000B3Q00061200070030000100010004493Q0030000100120A0007000C4Q0017000800044Q00050005000800012Q002A000500023Q00061200050047000100010004493Q004700012Q002A000500044Q001F0005000100014Q00058Q000500056Q000500063Q00062Q0005003F00013Q0004493Q003F00012Q002A000500064Q002A000600073Q00106F0005000D00062Q002A000500074Q006C000500084Q002A000500093Q0006520005002F2Q013Q0004493Q002F2Q012Q002A0005000A4Q00560005000100010004493Q002F2Q012Q002A000500063Q0006520005002F2Q013Q0004493Q002F2Q012Q002A000500064Q002A000600083Q00106F0005000D00060004493Q002F2Q012Q002A0004000B3Q00062300020060000100040004493Q006000012Q005C000400014Q006C000400054Q002A000400023Q0006520004002F2Q013Q0004493Q002F2Q012Q002A0004000D4Q006D0004000100022Q006C0004000C4Q002A0004000C3Q0026510004005D0001000E0004493Q005D00012Q005000046Q005C000400014Q006C0004000E3Q0004493Q002F2Q012Q002A0004000F3Q0006230003007C000100040004493Q007C00012Q002A000400023Q0006520004007C00013Q0004493Q007C00012Q002A000400063Q0006520004002F2Q013Q0004493Q002F2Q012Q002A000400063Q00204500040004000D2Q002A000500073Q00062Q0004002F2Q0100050004493Q002F2Q012Q002A000400064Q0021000500073Q00102Q0004000D00054Q000400076Q000400086Q000400033Q00122Q0005000F3Q00122Q000600103Q00122Q000700116Q000800076Q0007000200024Q0006000600074Q00040006000100044Q002F2Q012Q002A000400103Q00062300030098000100040004493Q009800012Q002A000400023Q0006520004009800013Q0004493Q009800012Q002A000400063Q0006520004002F2Q013Q0004493Q002F2Q012Q002A000400063Q00204500040004000D2Q002A000500113Q00062Q0004002F2Q0100050004493Q002F2Q012Q002A000400064Q0021000500113Q00102Q0004000D00054Q000400116Q000400086Q000400033Q00122Q0005000F3Q00122Q000600103Q00122Q000700116Q000800116Q0007000200024Q0006000600074Q00040006000100044Q002F2Q012Q002A000400123Q000623000300C2000100040004493Q00C200012Q002A000400134Q0065000400044Q006C000400134Q002A000400133Q000652000400A400013Q0004493Q00A4000100120A000400083Q000612000400A5000100010004493Q00A5000100120A000400094Q002A000500033Q00120A000600124Q002A000700133Q000652000700AD00013Q0004493Q00AD000100120A000700133Q000612000700AE000100010004493Q00AE000100120A000700144Q0017000800044Q00050005000800012Q002A000500133Q0006520005002F2Q013Q0004493Q002F2Q012Q002A0005000E3Q0006520005002F2Q013Q0004493Q002F2Q012Q002A0005000C3Q0006520005002F2Q013Q0004493Q002F2Q012Q002A0005000C3Q0020450005000500152Q002A000600143Q0020450006000600150006230005002F2Q0100060004493Q002F2Q012Q002A000500044Q00560005000100010004493Q002F2Q012Q002A000400153Q000623000300D5000100040004493Q00D500012Q002A000400013Q00204A00040004000300122Q000600043Q00202Q00060006000200202Q0006000600054Q00040006000200062Q000400D8000100010004493Q00D800012Q002A000400013Q00204A00040004000300122Q000600043Q00202Q00060006000200202Q0006000600064Q00040006000200062Q000400D8000100010004493Q00D800012Q002A000400163Q000623000300EB000100040004493Q00EB00012Q002A000400023Q000652000400EB00013Q0004493Q00EB00012Q002A000400174Q0067000500186Q000500056Q00040004000500202Q0004000400164Q000400176Q000400186Q000500176Q0004000400054Q000400196Q000400033Q00122Q000500176Q000600193Q00122Q000700086Q00040007000100044Q002F2Q012Q002A0004001A3Q0006230003000B2Q0100040004493Q000B2Q012Q002A000400023Q0006520004000B2Q013Q0004493Q000B2Q012Q002A0004000B3Q001235000500043Q0020450005000500010020450005000500180006230004003Q0100050004493Q003Q01001235000400043Q00202C00040004000100202Q0004000400194Q0004000B6Q000400033Q00122Q0005001A3Q00122Q0006001B3Q00122Q000700086Q00040007000100044Q002F2Q01001235000400043Q00202C00040004000100202Q0004000400184Q0004000B6Q000400033Q00122Q0005001A3Q00122Q0006001C3Q00122Q000700086Q00040007000100044Q002F2Q012Q002A0004001B3Q0006230003002A2Q0100040004493Q002A2Q012Q002A000400013Q00204A00040004000300122Q000600043Q00202Q00060006000200202Q0006000600054Q00040006000200062Q0004001E2Q0100010004493Q001E2Q012Q002A000400013Q00205A00040004000300122Q000600043Q00202Q00060006000200202Q0006000600064Q00040006000200062Q0004002A2Q013Q0004493Q002A2Q012Q002A000400023Q000652000400242Q013Q0004493Q00242Q012Q002A0004000A4Q00560004000100010004493Q002F2Q012Q002A000400033Q00120C0005001D3Q00122Q0006001E3Q00122Q000700096Q00040007000100044Q002F2Q012Q002A0004001C3Q0006230003002F2Q0100040004493Q002F2Q012Q002A0004001D4Q00560004000100012Q00133Q00017Q00013Q00030D3Q0055736572496E70757454797065020C3Q0006520001000300013Q0004493Q000300012Q00133Q00013Q00204500023Q00012Q002A00035Q0006230002000B000100030004493Q000B00012Q005C00026Q006C000200014Q002A000200024Q00560002000100012Q00133Q00017Q000B3Q0003063Q00506172656E7403093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q004865616C7468028Q0003043Q005465616D03053Q007063612Q6C03013Q005803013Q0059030C3Q006D6F7573656D6F766572656C016C4Q002A00015Q0006520001006100013Q0004493Q006100012Q002A000100013Q0006520001006100013Q0004493Q006100012Q002A000100023Q0006520001006100013Q0004493Q006100012Q002A000100033Q0006520001006100013Q0004493Q006100012Q002A000100043Q0006520001006100013Q0004493Q006100012Q005C00016Q0040000200024Q002A000300053Q0006520003003A00013Q0004493Q003A00012Q002A000300053Q0020450003000300010006520003003A00013Q0004493Q003A00012Q002A000300053Q0020450003000300020006520003003A00013Q0004493Q003A00012Q002A000300064Q0003000400053Q00202Q0004000400024Q000500076Q0003000500024Q000200036Q000300053Q00202Q00030003000200202Q00030003000300122Q000500046Q00030005000200062Q0002003A00013Q0004493Q003A00010006520003003A00013Q0004493Q003A0001002045000400030005000E1D0006003A000100040004493Q003A00012Q002A000400083Q0006520004003900013Q0004493Q003900012Q002A000400053Q0020450004000400072Q002A000500093Q00204500050005000700062300040039000100050004493Q003900012Q005C00015Q0004493Q003A00012Q005C000100013Q0006120001003F000100010004493Q003F00012Q002A0003000A4Q00560003000100012Q00133Q00013Q001235000300083Q00066800043Q000100022Q002A3Q00044Q00173Q00024Q002B0003000200050006520003005D00013Q0004493Q005D00010006520005005D00013Q0004493Q005D00010020450006000400092Q000F000700033Q00202Q0007000700094Q00060006000700202Q00070004000A4Q000800033Q00202Q00080008000A4Q0007000700084Q0008000B6Q0008000600084Q0009000B6Q00090007000900122Q000A000B3Q00062Q000A005F00013Q0004493Q005F0001001235000A00083Q00123F000B000B6Q000C00086Q000D00096Q000A000D000100044Q005F00012Q002A0006000A4Q00560006000100012Q005700015Q0004493Q006900012Q002A000100013Q00061200010067000100010004493Q006700012Q002A000100053Q0006520001006900013Q0004493Q006900012Q002A0001000A4Q00560001000100012Q002A0001000C4Q00560001000100012Q00133Q00013Q00013Q00023Q0003123Q00576F726C64546F5363722Q656E506F696E7403083Q00506F736974696F6E00074Q00637Q00206Q00014Q000200013Q00202Q0002000200026Q00029Q008Q00017Q00013Q00030B3Q004669656C644F6656696577010B4Q002800018Q0001000100014Q00018Q000100016Q000100023Q00062Q0001000A00013Q0004493Q000A00012Q002A000100024Q002A000200033Q00106F0001000100022Q00133Q00019Q002Q0001054Q001900018Q0001000100014Q00018Q000100018Q00017Q00013Q0003093Q00436861726163746572000B4Q002A7Q0020455Q00010006523Q000A00013Q0004493Q000A00012Q002A3Q00013Q0006523Q000700013Q0004493Q000700012Q002A3Q00023Q0006523Q000A00013Q0004493Q000A00012Q00133Q00017Q00", GetFEnv(), ...);
