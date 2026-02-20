--!native
--!optimize 2
--!strict

local ReadU8 = @[native, checked] function(Buffer: buffer, Offset: number): (number, number)
	return buffer.readu8(Buffer, Offset), Offset + 1
end

local ReadB = @[native, checked] function(Buffer: buffer, Offset: number): (boolean, number)
	return buffer.readu8(Buffer, Offset) > 0, Offset + 1
end

local ReadU32 = @[native, checked] function(Buffer: buffer, Offset: number): (number, number)
	return buffer.readu32(Buffer, Offset), Offset + 4
end

local ReadI32 = @[native, checked] function(Buffer: buffer, Offset: number): (number, number)
	return buffer.readi32(Buffer, Offset), Offset + 4
end

local ReadF64 = @[native, checked] function(Buffer: buffer, Offset: number): (number, number)
	return buffer.readf64(Buffer, Offset), Offset + 8
end

local ReadF32 = @[native, checked] function(Buffer: buffer, Offset: number): (number, number)
	return buffer.readf32(Buffer, Offset), Offset + 4
end

local ReadString = @[native, checked] function(Buffer: buffer, Offset: number, Count: number): (string, number)
	return buffer.readstring(Buffer, Offset, Count), Offset + Count
end

local ReadBytes = @[native, checked] function(Buffer: buffer, Offset: number, Count: number): (buffer, number)
	local NewBuffer = buffer.create(Count)
	buffer.copy(NewBuffer, 0, Buffer, Offset, Count)
	return NewBuffer, Offset + Count
end

local ReadVarInt = @[native, checked] function(Buffer: buffer, Offset: number): (number, number)
	local Result = 0
	local Shift = 0
	local CurrentOffset = Offset

	while true do
		local Byte = buffer.readu8(Buffer, CurrentOffset)
		CurrentOffset += 1
		local Val = bit32.band(Byte, 127)
		Result = bit32.bor(Result, bit32.lshift(Val, Shift))
		if bit32.band(Byte, 128) == 0 then
			break
		end
		Shift += 7
	end

	return Result, CurrentOffset
end

local ReadStringRef = @[native, checked] function(Buffer: buffer, Offset: number, StringTable: {string}): (string?, number)
	local Id = 0
	Id, Offset = ReadVarInt(Buffer, Offset)
	if Id == 0 then
		return nil, Offset
	end
	return StringTable[Id], Offset
end

type Upvalue = {
	value: any,
	store: {any}?,
	index: number?,
}

type ProtoInfo = typeof(table.freeze({} :: {
	Code: buffer,
	SizeCode: number,
	Constants: {any},
	ChildProtos: {any},
	NumParams: number,
	IsVarArg: boolean,
	MaxStackSize: number,
	NUps: number,
	LineDefined: number,
	DebugName: string?,
}))

local isFalse = @[native, checked] function (v: any): boolean
	return v == nil or v == false
end

local storeResults = @[native, checked] function(stack: {any}, baseReg: number, nresults: number, results: {any}, numResults: number, MaxStackSize: number)
	if nresults == -1 then
		for i = 1, numResults do
			stack[baseReg + i] = results[i]
		end
		for i = numResults + 1, MaxStackSize - baseReg do
			stack[baseReg + i] = nil
		end
		;(stack :: any)._top = baseReg + numResults
	else
		for i = 1, nresults do
			stack[baseReg + i] = if i <= numResults then results[i] else nil
		end
	end
end

@[native, checked] local function ExecuteProto(protoInfo: ProtoInfo, env: {[any]: any}, upvals: {Upvalue}, args: {any}, numArgs: number): ...any
	local Code = protoInfo.Code
	local Constants = protoInfo.Constants
	local ChildProtos = protoInfo.ChildProtos
	local NumParams = protoInfo.NumParams
	local IsVarArg = protoInfo.IsVarArg
	local MaxStackSize = protoInfo.MaxStackSize
	local CodeLen = buffer.len(Code)

	local stack: {any} = table.create(MaxStackSize)
	local varargs: {any}
	local varargCount: number = 0

	local paramCount = if numArgs < NumParams then numArgs else NumParams
	for i = 1, paramCount do
		stack[i] = args[i]
	end

	if IsVarArg then
		varargCount = numArgs - NumParams
		if varargCount > 0 then
			varargs = table.create(varargCount)
			for i = 1, varargCount do
				varargs[i] = args[NumParams + i]
			end
		else
			varargCount = 0
			varargs = {}
		end
	else
		varargs = {}
		varargCount = 0
	end

	local openUpvalues: {[number]: Upvalue} = {}

	local closeUpvalues = @[native, checked] function(fromReg: number): ()
	for reg, uv in openUpvalues do
		if reg >= fromReg then
			uv.value = stack[reg]
			uv.store = nil
			uv.index = nil
			openUpvalues[reg] = nil :: any
		end
	end
end

local findUpvalue = @[native, checked] function(reg: number): Upvalue
	local existing = openUpvalues[reg]
	if existing then
		return existing
	end
	local uv: Upvalue = {
		value = nil,
		store = stack :: any,
		index = reg,
	}
	openUpvalues[reg] = uv
	return uv
end

local getUpval = @[native, checked] function(uv: Upvalue): any
	if uv.store then
		return (uv.store :: {any})[uv.index :: number]
	end
	return uv.value
end

local setUpval = @[native, checked] function(uv: Upvalue, val: any)
	if uv.store then
		(uv.store :: {any})[uv.index :: number] = val
	else
		uv.value = val
	end
end

local readInsn = @[native, checked] function(atPc: number): number
	return buffer.readu32(Code, atPc * 4)
end

local signedD = @[native, checked] function(insn: number): number
	local d = bit32.rshift(insn, 16)
	if d >= 0x8000 then
		d -= 0x10000
	end
	return d
end

local signedE = @[native, checked] function(insn: number): number
	local e = bit32.rshift(insn, 8)
	if e >= 0x800000 then
		e -= 0x1000000
	end
	return e
end

local pc = 0

while true do
	if pc * 4 >= CodeLen then
		return
	end

	local insn = readInsn(pc)
	pc += 1
	local op = bit32.band(insn, 0xFF)

	if op == 0 then
		-- LOP_NOP

	elseif op == 1 then
		-- LOP_BREAK

	elseif op == 2 then
		-- LOP_LOADNIL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		stack[a + 1] = nil

	elseif op == 3 then
		-- LOP_LOADB
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = b ~= 0
		pc += c

	elseif op == 4 then
		-- LOP_LOADN
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		stack[a + 1] = d

	elseif op == 5 then
		-- LOP_LOADK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		stack[a + 1] = Constants[d + 1]

	elseif op == 6 then
		-- LOP_MOVE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		stack[a + 1] = stack[b + 1]

	elseif op == 7 then
		-- LOP_GETGLOBAL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local aux = readInsn(pc)
		pc += 1
		local key = Constants[aux + 1]
		stack[a + 1] = env[key]

	elseif op == 8 then
		-- LOP_SETGLOBAL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local aux = readInsn(pc)
		pc += 1
		local key = Constants[aux + 1]
		env[key] = stack[a + 1]

	elseif op == 9 then
		-- LOP_GETUPVAL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		stack[a + 1] = getUpval(upvals[b + 1])

	elseif op == 10 then
		-- LOP_SETUPVAL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		setUpval(upvals[b + 1], stack[a + 1])

	elseif op == 11 then
		-- LOP_CLOSEUPVALS
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		closeUpvalues(a + 1)

	elseif op == 12 then
		-- LOP_GETIMPORT
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local kv = Constants[d + 1]
		local aux = readInsn(pc)
		pc += 1

		if kv ~= nil then
			stack[a + 1] = kv
		else
			local count = bit32.rshift(aux, 30)
			local id0 = bit32.band(bit32.rshift(aux, 20), 1023) + 1
			local id1 = bit32.band(bit32.rshift(aux, 10), 1023) + 1
			local id2 = bit32.band(aux, 1023) + 1

			local result: any = nil
			local ok = pcall(function()
				result = env[Constants[id0]]
				if count >= 2 and result ~= nil then
					result = result[Constants[id1]]
				end
				if count >= 3 and result ~= nil then
					result = result[Constants[id2]]
				end
			end)
			if not ok then result = nil end
			stack[a + 1] = result
		end

	elseif op == 13 then
		-- LOP_GETTABLE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1][stack[c + 1]]

	elseif op == 14 then
		-- LOP_SETTABLE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[b + 1][stack[c + 1]] = stack[a + 1]

	elseif op == 15 then
		-- LOP_GETTABLEKS
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local aux = readInsn(pc)
		pc += 1
		local key = Constants[aux + 1]
		stack[a + 1] = stack[b + 1][key]

	elseif op == 16 then
		-- LOP_SETTABLEKS
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local aux = readInsn(pc)
		pc += 1
		local key = Constants[aux + 1]
		stack[b + 1][key] = stack[a + 1]

	elseif op == 17 then
		-- LOP_GETTABLEN
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1][c + 1]

	elseif op == 18 then
		-- LOP_SETTABLEN
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[b + 1][c + 1] = stack[a + 1]

	elseif op == 19 then
		-- LOP_NEWCLOSURE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = bit32.rshift(insn, 16) -- unsigned D for proto index
		local childProto = ChildProtos[d + 1] :: ProtoInfo
		local nups = childProto.NUps
		local closureUpvals = table.create(nups) :: {Upvalue}

		for i = 1, nups do
			local uinsn = readInsn(pc)
			pc += 1
			-- LOP_CAPTURE: A = capture type, B = register/upvalue index
			local captureType = bit32.band(bit32.rshift(uinsn, 8), 0xFF)
			local captureReg = bit32.band(bit32.rshift(uinsn, 16), 0xFF)

			if captureType == 0 then -- LCT_VAL
				closureUpvals[i] = { value = stack[captureReg + 1], store = nil, index = nil }
			elseif captureType == 1 then -- LCT_REF
				closureUpvals[i] = findUpvalue(captureReg + 1)
			elseif captureType == 2 then -- LCT_UPVAL
				closureUpvals[i] = upvals[captureReg + 1]
			end
		end

		local proto = childProto
		local childEnv = env
		local closureUpvalsRef = closureUpvals
		local function closure(...: any): ...any
			local callArgs = table.pack(...)
			return ExecuteProto(proto, childEnv, closureUpvalsRef, callArgs, callArgs.n)
		end
		stack[a + 1] = closure

	elseif op == 20 then
		-- LOP_NAMECALL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local aux = readInsn(pc)
		pc += 1
		local key = Constants[aux + 1]
		local obj = stack[b + 1]
		stack[a + 2] = obj
		stack[a + 1] = obj[key]

	elseif op == 21 then
		-- LOP_CALL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		local nparams = b - 1
		local nresults = c - 1
		local func = stack[a + 1]

		local callArgs: {any}
		local actualParams: number

		if nparams == -1 then
			local top = (stack :: any)._top
			if top == nil then top = a end
			actualParams = top - a
			if actualParams < 0 then actualParams = 0 end
			callArgs = table.create(actualParams)
			for i = 1, actualParams do
				callArgs[i] = stack[a + 1 + i]
			end
		else
			actualParams = nparams
			callArgs = table.create(nparams)
			for i = 1, nparams do
				callArgs[i] = stack[a + 1 + i]
			end
		end

		local packedResults = table.pack(func(table.unpack(callArgs, 1, actualParams)))
		local numResults = packedResults.n
		storeResults(stack, a, nresults, packedResults, numResults, MaxStackSize)

	elseif op == 22 then
		-- LOP_RETURN
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local nresults = b - 1

		closeUpvalues(1)

		if nresults == -1 then
			local top = (stack :: any)._top
			if top == nil then top = a end
			local count = top - a
			if count <= 0 then return end
			local retVals = table.create(count)
			for i = 1, count do retVals[i] = stack[a + i] end
			return table.unpack(retVals, 1, count)
		elseif nresults == 0 then
			return
		else
			local retVals = table.create(nresults)
			for i = 1, nresults do retVals[i] = stack[a + i] end
			return table.unpack(retVals, 1, nresults)
		end

	elseif op == 23 then
		-- LOP_JUMP
		local d = signedD(insn)
		pc += d

	elseif op == 24 then
		-- LOP_JUMPBACK
		local d = signedD(insn)
		pc += d

	elseif op == 25 then
		-- LOP_JUMPIF
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		if not isFalse(stack[a + 1]) then
			pc += d
		end

	elseif op == 26 then
		-- LOP_JUMPIFNOT
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		if isFalse(stack[a + 1]) then
			pc += d
		end

	elseif op == 27 then
		-- LOP_JUMPIFEQ
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		if stack[a + 1] == stack[bit32.band(aux, 0xFF) + 1] then
			pc += d
		else
			pc += 1
		end

	elseif op == 28 then
		-- LOP_JUMPIFLE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		if stack[a + 1] <= stack[bit32.band(aux, 0xFF) + 1] then
			pc += d
		else
			pc += 1
		end

	elseif op == 29 then
		-- LOP_JUMPIFLT
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		if stack[a + 1] < stack[bit32.band(aux, 0xFF) + 1] then
			pc += d
		else
			pc += 1
		end

	elseif op == 30 then
		-- LOP_JUMPIFNOTEQ
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		if stack[a + 1] ~= stack[bit32.band(aux, 0xFF) + 1] then
			pc += d
		else
			pc += 1
		end

	elseif op == 31 then
		-- LOP_JUMPIFNOTLE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		if not (stack[a + 1] <= stack[bit32.band(aux, 0xFF) + 1]) then
			pc += d
		else
			pc += 1
		end

	elseif op == 32 then
		-- LOP_JUMPIFNOTLT
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		if not (stack[a + 1] < stack[bit32.band(aux, 0xFF) + 1]) then
			pc += d
		else
			pc += 1
		end

	elseif op == 33 then
		-- LOP_ADD
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] + stack[c + 1]

	elseif op == 34 then
		-- LOP_SUB
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] - stack[c + 1]

	elseif op == 35 then
		-- LOP_MUL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] * stack[c + 1]

	elseif op == 36 then
		-- LOP_DIV
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] / stack[c + 1]

	elseif op == 37 then
		-- LOP_MOD
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] % stack[c + 1]

	elseif op == 38 then
		-- LOP_POW
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] ^ stack[c + 1]

	elseif op == 39 then
		-- LOP_ADDK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] + Constants[c + 1]

	elseif op == 40 then
		-- LOP_SUBK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] - Constants[c + 1]

	elseif op == 41 then
		-- LOP_MULK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] * Constants[c + 1]

	elseif op == 42 then
		-- LOP_DIVK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] / Constants[c + 1]

	elseif op == 43 then
		-- LOP_MODK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] % Constants[c + 1]

	elseif op == 44 then
		-- LOP_POWK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = stack[b + 1] ^ Constants[c + 1]

	elseif op == 45 then
		-- LOP_AND
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		local rb = stack[b + 1]
		stack[a + 1] = if isFalse(rb) then rb else stack[c + 1]

	elseif op == 46 then
		-- LOP_OR
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		local rb = stack[b + 1]
		stack[a + 1] = if isFalse(rb) then stack[c + 1] else rb

	elseif op == 47 then
		-- LOP_ANDK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		local rb = stack[b + 1]
		stack[a + 1] = if isFalse(rb) then rb else Constants[c + 1]

	elseif op == 48 then
		-- LOP_ORK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		local rb = stack[b + 1]
		stack[a + 1] = if isFalse(rb) then Constants[c + 1] else rb

	elseif op == 49 then
		-- LOP_CONCAT
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		local result = stack[b + 1]
		for i = b + 1, c do
			result = result .. stack[i + 1]
		end
		stack[a + 1] = result

	elseif op == 50 then
		-- LOP_NOT
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		stack[a + 1] = isFalse(stack[b + 1])

	elseif op == 51 then
		-- LOP_MINUS
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		stack[a + 1] = -stack[b + 1]

	elseif op == 52 then
		-- LOP_LENGTH
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		stack[a + 1] = #stack[b + 1]

	elseif op == 53 then
		-- LOP_NEWTABLE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		pc += 1 -- skip AUX (array size)
		stack[a + 1] = table.create(if b == 0 then 0 else bit32.lshift(1, b - 1))

	elseif op == 54 then
		-- LOP_DUPTABLE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local templateKeys = Constants[d + 1] :: {[number]: number}
		local newTable = {}
		for _, keyIdx in templateKeys do
			local key = Constants[keyIdx + 1]
			;(newTable :: any)[key] = nil
		end
		stack[a + 1] = newTable

	elseif op == 55 then
		-- LOP_SETLIST
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF) - 1
		local aux = readInsn(pc)
		pc += 1
		local index = aux
		local t = stack[a + 1]

		local count: number
		if c == -1 then
			local top = (stack :: any)._top
			if top == nil then top = b end
			count = top - b
			if count < 0 then count = 0 end
		else
			count = c
		end
		for i = 0, count - 1 do
			t[index + i + 1] = stack[b + 1 + i]
		end

	elseif op == 56 then
		-- LOP_FORNPREP
		-- Register layout: [limit, step, index, variable]
		-- R(A) = limit, R(A+1) = step, R(A+2) = index
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local limit = tonumber(stack[a + 1]) :: number
		local step = tonumber(stack[a + 2]) :: number
		local idx = tonumber(stack[a + 3]) :: number
		stack[a + 1] = limit
		stack[a + 2] = step
		stack[a + 3] = idx

		if not (step > 0 and idx <= limit or step <= 0 and limit <= idx) then
			pc += d
		end

	elseif op == 57 then
		-- LOP_FORNLOOP
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local limit = stack[a + 1] :: number
		local step = stack[a + 2] :: number
		local idx = stack[a + 3] + step
		stack[a + 3] = idx

		if step > 0 and idx <= limit or step <= 0 and limit <= idx then
			pc += d
		end

	elseif op == 58 then
		-- LOP_FORGLOOP
		-- Register layout: [generator, state, index, variables...]
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		local numVars = bit32.band(aux, 0xFF)
		local iterFunc = stack[a + 1]
		local state = stack[a + 2]
		local controlVar = stack[a + 3]

		local results = table.pack(iterFunc(state, controlVar))

		if bit32.btest(aux, 0x80000000) then
			-- ipairs-style fast path indicator
			numVars = 2
		end

		if results[1] == nil then
			pc += 1 -- skip aux, exit loop
		else
			stack[a + 3] = results[1] -- update index (control variable)
			for i = 1, numVars do
				stack[a + 2 + i] = results[i]
			end
			pc += d -- jump back to loop header
		end

	elseif op == 59 then
		-- LOP_FORGPREP_INEXT
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		-- Set up ipairs iterator
		local tbl = stack[a + 2]
		local iter, st, ctrl = ipairs(tbl)
		stack[a + 1] = iter
		stack[a + 2] = st
		stack[a + 3] = ctrl
		pc += d

	elseif op == 60 then
		-- LOP_FASTCALL3
		-- Skip: the CALL that follows will handle execution
		pc += 1 -- skip AUX

	elseif op == 61 then
		-- LOP_FORGPREP_NEXT
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local tbl = stack[a + 2]
		local iter, st, ctrl = pairs(tbl)
		stack[a + 1] = iter
		stack[a + 2] = st
		stack[a + 3] = ctrl
		pc += d

	elseif op == 62 then
		-- LOP_NATIVECALL
		error("NATIVECALL is not supported")

	elseif op == 63 then
		-- LOP_GETVARARGS
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF) - 1

		if b == -1 then
			-- MULTRET: copy all varargs
			for i = 1, varargCount do
				stack[a + i] = varargs[i]
			end
			for i = varargCount + 1, MaxStackSize - a do
				stack[a + i] = nil
			end
			;(stack :: any)._top = a + varargCount
		else
			for i = 1, b do
				stack[a + i] = if i <= varargCount then varargs[i] else nil
			end
		end

	elseif op == 64 then
		-- LOP_DUPCLOSURE
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local protoRef = Constants[d + 1]
		local childProto: ProtoInfo

		if type(protoRef) == "function" then
			error("DUPCLOSURE: unexpected function constant")
		else
			childProto = protoRef :: ProtoInfo
		end

		local nups = childProto.NUps
		local closureUpvals = table.create(nups) :: {Upvalue}

		for i = 1, nups do
			local uinsn = readInsn(pc)
			pc += 1
			local captureType = bit32.band(bit32.rshift(uinsn, 8), 0xFF)
			local captureReg = bit32.band(bit32.rshift(uinsn, 16), 0xFF)

			if captureType == 0 then
				closureUpvals[i] = { value = stack[captureReg + 1], store = nil, index = nil }
			elseif captureType == 1 then
				closureUpvals[i] = findUpvalue(captureReg + 1)
			elseif captureType == 2 then
				closureUpvals[i] = upvals[captureReg + 1]
			else
				error(`DUPCLOSURE: unexpected capture type {captureType}`)
			end
		end

		local proto = childProto
		local childEnv = env
		local closureUpvalsRef = closureUpvals
		local function closure(...: any): ...any
			local callArgs = table.pack(...)
			return ExecuteProto(proto, childEnv, closureUpvalsRef, callArgs, callArgs.n)
		end
		stack[a + 1] = closure

	elseif op == 65 then
		-- LOP_PREPVARARGS: no-op (handled during setup)

	elseif op == 66 then
		-- LOP_LOADKX
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local aux = readInsn(pc)
		pc += 1
		stack[a + 1] = Constants[aux + 1]

	elseif op == 67 then
		-- LOP_JUMPX
		local e = signedE(insn)
		pc += e

	elseif op == 68 then
		-- LOP_FASTCALL: no-op, CALL handles it

	elseif op == 69 then
		-- LOP_COVERAGE: no-op

	elseif op == 70 then
		-- LOP_CAPTURE
		error("CAPTURE executed outside of NEWCLOSURE")

	elseif op == 71 then
		-- LOP_SUBRK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = Constants[b + 1] - stack[c + 1]

	elseif op == 72 then
		-- LOP_DIVRK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = Constants[b + 1] / stack[c + 1]

	elseif op == 73 then
		-- LOP_FASTCALL1: no-op

	elseif op == 74 then
		-- LOP_FASTCALL2: skip AUX
		pc += 1

	elseif op == 75 then
		-- LOP_FASTCALL2K: skip AUX
		pc += 1

	elseif op == 76 then
		-- LOP_FORGPREP
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local iterVal = stack[a + 1]

		if type(iterVal) == "function" then
			-- already a function, nothing to do
		elseif type(iterVal) == "table" then
			stack[a + 1] = next
			stack[a + 2] = iterVal
			stack[a + 3] = nil
		else
			error(`attempt to iterate over a {typeof(iterVal)} value`)
		end
		pc += d

	elseif op == 77 then
		-- LOP_JUMPXEQKNIL
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		local notBit = bit32.btest(aux, 0x80000000)
		local isNil = stack[a + 1] == nil
		pc += if isNil ~= notBit then d else 1
	elseif op == 78 then
		-- LOP_JUMPXEQKB
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		local kbVal = bit32.btest(aux, 1)
		local notBit = bit32.btest(aux, 0x80000000)
		local ra = stack[a + 1]
		local matches = type(ra) == "boolean" and ra == kbVal
		pc += if matches ~= notBit then d else 1

	elseif op == 79 then
		-- LOP_JUMPXEQKN
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		local kvIdx = bit32.band(aux, 0xFFFFFF)
		local notBit = bit32.btest(aux, 0x80000000)
		local kv = Constants[kvIdx + 1]
		local ra = stack[a + 1]
		local matches = type(ra) == "number" and ra == kv

		pc += if matches ~= notBit then d else 1

	elseif op == 80 then
		-- LOP_JUMPXEQKS
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local d = signedD(insn)
		local aux = readInsn(pc)
		local kvIdx = bit32.band(aux, 0xFFFFFF)
		local notBit = bit32.btest(aux, 0x80000000)
		local kv = Constants[kvIdx + 1]
		local ra = stack[a + 1]
		local matches = type(ra) == "string" and ra == kv

		pc += if matches ~= notBit then d else 1

	elseif op == 81 then
		-- LOP_IDIV
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = (stack[b + 1] :: any) // (stack[c + 1] :: any)

	elseif op == 82 then
		-- LOP_IDIVK
		local a = bit32.band(bit32.rshift(insn, 8), 0xFF)
		local b = bit32.band(bit32.rshift(insn, 16), 0xFF)
		local c = bit32.band(bit32.rshift(insn, 24), 0xFF)
		stack[a + 1] = (stack[b + 1] :: any) // (Constants[c + 1] :: any)

	else
		error(`Unknown opcode: {op}`)
	end
end

return
	end

local luau_load = @[native, checked] function(Bytecode: buffer, Env: {[any]: any}): ((...any) -> ...any)
	local Offset = 0

	local LuauVersion = 0
	LuauVersion, Offset = ReadU8(Bytecode, Offset)

	if LuauVersion == 0 then
		local ErrorMessage = buffer.readstring(Bytecode, Offset, buffer.len(Bytecode) - Offset)
		error(ErrorMessage)
	end

	if LuauVersion < 3 or LuauVersion > 6 then
		error(`bytecode version mismatch (expected [3..6], got {LuauVersion})`)
	end

	local TypesVersion = 0

	if LuauVersion >= 4 then
		TypesVersion, Offset = ReadU8(Bytecode, Offset)
		if TypesVersion < 1 or TypesVersion > 3 then
			error(`bytecode type version mismatch (expected [1..3], got {TypesVersion})`)
		end
	end

	local StringCount = 0
	StringCount, Offset = ReadVarInt(Bytecode, Offset)
	local StringTable = table.create(StringCount) :: {string}
	for i = 1, StringCount do
		local StrLength = 0
		StrLength, Offset = ReadVarInt(Bytecode, Offset)
		local Str = ""
		Str, Offset = ReadString(Bytecode, Offset, StrLength)
		StringTable[i] = Str
	end

	table.freeze(StringTable)

	if TypesVersion == 3 then
		local Index = 0
		Index, Offset = ReadU8(Bytecode, Offset)
		while Index ~= 0 do
			local _name: string?
			_name, Offset = ReadStringRef(Bytecode, Offset, StringTable)
			Index, Offset = ReadU8(Bytecode, Offset)
		end
	end

	local ProtoCount = 0
	ProtoCount, Offset = ReadVarInt(Bytecode, Offset)
	local ProtoInfos = table.create(ProtoCount) :: typeof(table.freeze({} :: {ProtoInfo}))

	for i = 1, ProtoCount do
		local MaxStackSize = 0
		MaxStackSize, Offset = ReadU8(Bytecode, Offset)

		local NumParams = 0
		NumParams, Offset = ReadU8(Bytecode, Offset)

		local NUps = 0
		NUps, Offset = ReadU8(Bytecode, Offset)

		local IsVarArgByte = 0
		IsVarArgByte, Offset = ReadU8(Bytecode, Offset)
		local IsVarArg = IsVarArgByte > 0

		local Flags = 0

		if LuauVersion >= 4 then
			Flags, Offset = ReadU8(Bytecode, Offset)

			if TypesVersion == 1 then
				local TypeSize = 0
				TypeSize, Offset = ReadVarInt(Bytecode, Offset)
				Offset += TypeSize
			elseif TypesVersion == 2 or TypesVersion == 3 then
				local TypeSize = 0
				TypeSize, Offset = ReadVarInt(Bytecode, Offset)
				Offset += TypeSize
			end
		end

		local SizeCode = 0
		SizeCode, Offset = ReadVarInt(Bytecode, Offset)

		local Code: buffer
		Code, Offset = ReadBytes(Bytecode, Offset, SizeCode * 4)

		local SizeConstants = 0
		SizeConstants, Offset = ReadVarInt(Bytecode, Offset)
		local Constants = table.create(SizeConstants) :: {any}

		for j = 1, SizeConstants do
			local ConstType = 0
			ConstType, Offset = ReadU8(Bytecode, Offset)

			if ConstType == 0 then
				-- LBC_CONSTANT_NIL
			elseif ConstType == 1 then
				-- LBC_CONSTANT_BOOLEAN
				local Value = false
				Value, Offset = ReadB(Bytecode, Offset)
				Constants[j] = Value
			elseif ConstType == 2 then
				-- LBC_CONSTANT_NUMBER
				local Value = 0
				Value, Offset = ReadF64(Bytecode, Offset)
				Constants[j] = Value
			elseif ConstType == 7 then
				-- LBC_CONSTANT_VECTOR
				local X = 0; X, Offset = ReadF32(Bytecode, Offset)
				local Y = 0; Y, Offset = ReadF32(Bytecode, Offset)
				local Z = 0; Z, Offset = ReadF32(Bytecode, Offset)
				local W = 0; W, Offset = ReadF32(Bytecode, Offset)
				Constants[j] = vector.create(X, Y, Z)
			elseif ConstType == 3 then
				-- LBC_CONSTANT_STRING
				local Id = 0
				Id, Offset = ReadVarInt(Bytecode, Offset)
				Constants[j] = StringTable[Id]
			elseif ConstType == 4 then
				-- LBC_CONSTANT_IMPORT
				local iid = 0
				iid, Offset = ReadU32(Bytecode, Offset)
				local Count = bit32.rshift(iid, 30)
				local id0 = bit32.band(bit32.rshift(iid, 20), 1023) + 1
				local id1 = bit32.band(bit32.rshift(iid, 10), 1023) + 1
				local id2 = bit32.band(iid, 1023) + 1

				local result: any = nil
				local ok = pcall(function()
					local key0 = Constants[id0]
					result = Env[key0]
					if Count >= 2 and result ~= nil then
						local key1 = Constants[id1]
						result = result[key1]
					end
					if Count >= 3 and result ~= nil then
						local key2 = Constants[id2]
						result = result[key2]
					end
				end)
				if not ok then result = nil end
				Constants[j] = result
			elseif ConstType == 5 then
				-- LBC_CONSTANT_TABLE
				local Keys = 0
				Keys, Offset = ReadVarInt(Bytecode, Offset)
				local Table = {} :: {[number]: number}
				for _k = 1, Keys do
					local Key = 0
					Key, Offset = ReadVarInt(Bytecode, Offset)
					Table[_k] = Key
				end
				Constants[j] = Table
			elseif ConstType == 6 then
				-- LBC_CONSTANT_CLOSURE
				local fid = 0
				fid, Offset = ReadVarInt(Bytecode, Offset)
				Constants[j] = ProtoInfos[fid + 1]
			else
				error("Unexpected constant kind")
			end
		end

		local ChildProtoCount = 0
		ChildProtoCount, Offset = ReadVarInt(Bytecode, Offset)
		local ChildProtos = table.create(ChildProtoCount) :: {any}
		for j = 1, ChildProtoCount do
			local fid = 0
			fid, Offset = ReadVarInt(Bytecode, Offset)
			ChildProtos[j] = ProtoInfos[fid + 1]
		end

		local LineDefined = 0
		LineDefined, Offset = ReadVarInt(Bytecode, Offset)

		local DebugName: string?
		DebugName, Offset = ReadStringRef(Bytecode, Offset, StringTable)

		local HasLineInfo = false
		HasLineInfo, Offset = ReadB(Bytecode, Offset)

		if HasLineInfo then
			local LineGapLog2 = 0
			LineGapLog2, Offset = ReadU8(Bytecode, Offset)
			local Intervals = bit32.rshift(SizeCode - 1, LineGapLog2) + 1

			local LastOffset = 0
			for j = 0, SizeCode - 1 do
				local LineOffset = 0
				LineOffset, Offset = ReadU8(Bytecode, Offset)
				LastOffset += LineOffset
			end

			local LastLine = 0
			for j = 0, Intervals - 1 do
				local AbsLine = 0
				AbsLine, Offset = ReadI32(Bytecode, Offset)
				LastLine += AbsLine
			end
		end

		local HasDebugInfo = false
		HasDebugInfo, Offset = ReadB(Bytecode, Offset)

		if HasDebugInfo then
			local SizeLocVars = 0
			SizeLocVars, Offset = ReadVarInt(Bytecode, Offset)
			for j = 1, SizeLocVars do
				local _VarName: string?
				_VarName, Offset = ReadStringRef(Bytecode, Offset, StringTable)
				local _StartPC = 0
				_StartPC, Offset = ReadVarInt(Bytecode, Offset)
				local _EndPC = 0
				_EndPC, Offset = ReadVarInt(Bytecode, Offset)
				local _Reg = 0
				_Reg, Offset = ReadU8(Bytecode, Offset)
			end

			local SizeUpvalues = 0
			SizeUpvalues, Offset = ReadVarInt(Bytecode, Offset)
			for j = 1, SizeUpvalues do
				local _UpvalName: string?
				_UpvalName, Offset = ReadStringRef(Bytecode, Offset, StringTable)
			end
		end

		local protoInfo = table.freeze({
			Code = Code,
			SizeCode = SizeCode,
			Constants = Constants,
			ChildProtos = ChildProtos,
			NumParams = NumParams,
			IsVarArg = IsVarArg,
			MaxStackSize = MaxStackSize,
			NUps = NUps,
			LineDefined = LineDefined,
			DebugName = DebugName,
		} :: ProtoInfo)

		ProtoInfos[i] = protoInfo
	end
	table.freeze(ProtoInfos)

	local MainId = 0
	MainId, Offset = ReadVarInt(Bytecode, Offset)
	local MainProtoInfo = ProtoInfos[MainId + 1]

	return @[native, checked] function(...: any): ...any
	local args = table.pack(...)
	local mainUpvals = table.create(MainProtoInfo.NUps) :: {Upvalue}
	for i = 1, MainProtoInfo.NUps do
		mainUpvals[i] = { value = Env, store = nil, index = nil }
	end
	return ExecuteProto(MainProtoInfo, Env, mainUpvals, args, args.n)
end
end

return table.freeze({
	luau_load = luau_load,
})
