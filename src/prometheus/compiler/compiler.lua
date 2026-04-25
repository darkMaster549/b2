-- Prometheus Obfuscator by Levno_710 -- Compiler (VM engine for Vmify step)
local MAX_REGS = 100
local MAX_REGS_MUL = 0

local Ast          = require("prometheus.ast")
local Scope        = require("prometheus.scope")
local logger       = require("logger")
local util         = require("prometheus.util")
local visitast     = require("prometheus.visitast")
local randomStrings = require("prometheus.randomStrings")

local lookupify = util.lookupify
local AstKind   = Ast.AstKind
local unpack    = unpack or table.unpack

local Compiler = {}

function Compiler:new()
    local c = {
        blocks = {}; registers = {}; activeBlock = nil;
        registersForVar = {}; usedRegisters = 0; maxUsedRegister = 0; registerVars = {};
        VAR_REGISTER    = {};
        RETURN_ALL      = {};
        POS_REGISTER    = {};
        RETURN_REGISTER = {};
        UPVALUE         = {};
        BIN_OPS = lookupify{
            AstKind.LessThanExpression, AstKind.GreaterThanExpression,
            AstKind.LessThanOrEqualsExpression, AstKind.GreaterThanOrEqualsExpression,
            AstKind.NotEqualsExpression, AstKind.EqualsExpression,
            AstKind.StrCatExpression, AstKind.AddExpression, AstKind.SubExpression,
            AstKind.MulExpression, AstKind.DivExpression, AstKind.ModExpression, AstKind.PowExpression,
        };
    }
    setmetatable(c, self); self.__index = self
    return c
end

function Compiler:createBlock()
    local id
    repeat id = math.random(0, 2^24) until not self.usedBlockIds[id]
    local block = { id=id; statements={}; scope=Scope:new(self.containerFuncScope); advanceToNextBlock=true }
    table.insert(self.blocks, block)
    return block
end

function Compiler:setActiveBlock(block) self.activeBlock = block end

function Compiler:addStatement(statement, writes, reads, usesUpvals)
    if self.activeBlock.advanceToNextBlock then
        table.insert(self.activeBlock.statements, {
            statement=statement, writes=lookupify(writes),
            reads=lookupify(reads), usesUpvals=usesUpvals or false,
        })
    end
end

function Compiler:compile(ast)
    self.blocks={}; self.registers={}; self.activeBlock=nil; self.registersForVar={}
    self.scopeFunctionDepths={}; self.maxUsedRegister=0; self.usedRegisters=0
    self.registerVars={}; self.usedBlockIds={}; self.upvalVars={}; self.registerUsageStack={}
    self.upvalsProxyLenReturn = math.random(-2^22, 2^22)

    local newGlobalScope = Scope:newGlobal()
    local psc = Scope:new(newGlobalScope, nil)

    local _,getfenvVar    = newGlobalScope:resolve("getfenv")
    local _,tableVar      = newGlobalScope:resolve("table")
    local _,unpackVar     = newGlobalScope:resolve("unpack")
    local _,envVar        = newGlobalScope:resolve("_ENV")
    local _,setmetaVar    = newGlobalScope:resolve("setmetatable")
    local _,selectVar     = newGlobalScope:resolve("select")

    psc:addReferenceToHigherScope(newGlobalScope, getfenvVar, 2)
    psc:addReferenceToHigherScope(newGlobalScope, tableVar)
    psc:addReferenceToHigherScope(newGlobalScope, unpackVar)
    psc:addReferenceToHigherScope(newGlobalScope, envVar)
    psc:addReferenceToHigherScope(newGlobalScope, setmetaVar)

    self.scope           = Scope:new(psc)
    self.envVar          = self.scope:addVariable()
    self.containerFuncVar= self.scope:addVariable()
    self.unpackVar       = self.scope:addVariable()
    self.setmetatableVar = self.scope:addVariable()
    self.selectVar       = self.scope:addVariable()
    local argVar         = self.scope:addVariable()

    self.containerFuncScope = Scope:new(self.scope)
    self.whileScope         = Scope:new(self.containerFuncScope)
    self.posVar             = self.containerFuncScope:addVariable()
    self.argsVar            = self.containerFuncScope:addVariable()
    self.currentUpvaluesVar = self.containerFuncScope:addVariable()
    self.detectGcCollectVar = self.containerFuncScope:addVariable()
    self.returnVar          = self.containerFuncScope:addVariable()

    self.upvaluesTable               = self.scope:addVariable()
    self.upvaluesReferenceCountsTable= self.scope:addVariable()
    self.allocUpvalFunction          = self.scope:addVariable()
    self.currentUpvalId              = self.scope:addVariable()
    self.upvaluesProxyFunctionVar    = self.scope:addVariable()
    self.upvaluesGcFunctionVar       = self.scope:addVariable()
    self.freeUpvalueFunc             = self.scope:addVariable()
    self.createClosureVars           = {}
    self.createVarargClosureVar      = self.scope:addVariable()

    local createClosureScope    = Scope:new(self.scope)
    local createClosurePosArg   = createClosureScope:addVariable()
    local createClosureUpvalsArg= createClosureScope:addVariable()
    local createClosureProxyObj = createClosureScope:addVariable()
    local createClosureFuncVar  = createClosureScope:addVariable()
    local createClosureSubScope = Scope:new(createClosureScope)

    local upvalEntries, upvalueIds = {}, {}
    self.getUpvalueId = function(self, scope, id)
        if upvalueIds[id] then return upvalueIds[id] end
        local expression
        if self.scopeFunctionDepths[scope] == 0 then
            expression = Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.allocUpvalFunction), {})
        else
            logger:error("Unresolved Upvalue")
        end
        table.insert(upvalEntries, Ast.TableEntry(expression))
        local uid = #upvalEntries
        upvalueIds[id] = uid
        return uid
    end

    createClosureSubScope:addReferenceToHigherScope(self.scope, self.containerFuncVar)
    createClosureSubScope:addReferenceToHigherScope(createClosureScope, createClosurePosArg)
    createClosureSubScope:addReferenceToHigherScope(createClosureScope, createClosureUpvalsArg, 1)
    createClosureScope:addReferenceToHigherScope(self.scope, self.upvaluesProxyFunctionVar)
    createClosureSubScope:addReferenceToHigherScope(createClosureScope, createClosureProxyObj)

    self:compileTopNode(ast)

    local fnAssignments = {
        { var=Ast.AssignmentVariable(self.scope, self.containerFuncVar),
          val=Ast.FunctionLiteralExpression({
              Ast.VariableExpression(self.containerFuncScope, self.posVar),
              Ast.VariableExpression(self.containerFuncScope, self.argsVar),
              Ast.VariableExpression(self.containerFuncScope, self.currentUpvaluesVar),
              Ast.VariableExpression(self.containerFuncScope, self.detectGcCollectVar),
          }, self:emitContainerFuncBody()) },
        { var=Ast.AssignmentVariable(self.scope, self.createVarargClosureVar),
          val=Ast.FunctionLiteralExpression({
              Ast.VariableExpression(createClosureScope, createClosurePosArg),
              Ast.VariableExpression(createClosureScope, createClosureUpvalsArg),
          }, Ast.Block({
              Ast.LocalVariableDeclaration(createClosureScope, {createClosureProxyObj}, {
                  Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.upvaluesProxyFunctionVar), {
                      Ast.VariableExpression(createClosureScope, createClosureUpvalsArg)
                  })
              }),
              Ast.LocalVariableDeclaration(createClosureScope, {createClosureFuncVar}, {
                  Ast.FunctionLiteralExpression({Ast.VarargExpression()},
                      Ast.Block({Ast.ReturnStatement{
                          Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.containerFuncVar), {
                              Ast.VariableExpression(createClosureScope, createClosurePosArg),
                              Ast.TableConstructorExpression({Ast.TableEntry(Ast.VarargExpression())}),
                              Ast.VariableExpression(createClosureScope, createClosureUpvalsArg),
                              Ast.VariableExpression(createClosureScope, createClosureProxyObj),
                          })
                      }}, createClosureSubScope))
              }),
              Ast.ReturnStatement{Ast.VariableExpression(createClosureScope, createClosureFuncVar)},
          }, createClosureScope)) },
        { var=Ast.AssignmentVariable(self.scope, self.upvaluesTable),               val=Ast.TableConstructorExpression({}) },
        { var=Ast.AssignmentVariable(self.scope, self.upvaluesReferenceCountsTable),val=Ast.TableConstructorExpression({}) },
        { var=Ast.AssignmentVariable(self.scope, self.allocUpvalFunction),           val=self:createAllocUpvalFunction() },
        { var=Ast.AssignmentVariable(self.scope, self.currentUpvalId),               val=Ast.NumberExpression(0) },
        { var=Ast.AssignmentVariable(self.scope, self.upvaluesProxyFunctionVar),     val=self:createUpvaluesProxyFunc() },
        { var=Ast.AssignmentVariable(self.scope, self.upvaluesGcFunctionVar),        val=self:createUpvaluesGcFunc() },
        { var=Ast.AssignmentVariable(self.scope, self.freeUpvalueFunc),              val=self:createFreeUpvalueFunc() },
    }

    local tbl = {
        Ast.VariableExpression(self.scope, self.containerFuncVar),
        Ast.VariableExpression(self.scope, self.createVarargClosureVar),
        Ast.VariableExpression(self.scope, self.upvaluesTable),
        Ast.VariableExpression(self.scope, self.upvaluesReferenceCountsTable),
        Ast.VariableExpression(self.scope, self.allocUpvalFunction),
        Ast.VariableExpression(self.scope, self.currentUpvalId),
        Ast.VariableExpression(self.scope, self.upvaluesProxyFunctionVar),
        Ast.VariableExpression(self.scope, self.upvaluesGcFunctionVar),
        Ast.VariableExpression(self.scope, self.freeUpvalueFunc),
    }
    for _, entry in pairs(self.createClosureVars) do
        table.insert(fnAssignments, entry)
        table.insert(tbl, Ast.VariableExpression(entry.var.scope, entry.var.id))
    end

    util.shuffle(fnAssignments)
    local lhs, rhs = {}, {}
    for i,v in ipairs(fnAssignments) do lhs[i]=v.var; rhs[i]=v.val end

    local functionNode = Ast.FunctionLiteralExpression({
        Ast.VariableExpression(self.scope, self.envVar),
        Ast.VariableExpression(self.scope, self.unpackVar),
        Ast.VariableExpression(self.scope, self.setmetatableVar),
        Ast.VariableExpression(self.scope, self.selectVar),
        Ast.VariableExpression(self.scope, argVar),
        unpack(util.shuffle(tbl))
    }, Ast.Block({
        Ast.AssignmentStatement(lhs, rhs),
        Ast.ReturnStatement{
            Ast.FunctionCallExpression(Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.createVarargClosureVar), {
                Ast.NumberExpression(self.startBlockId),
                Ast.TableConstructorExpression(upvalEntries),
            }), {Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.unpackVar), {Ast.VariableExpression(self.scope, argVar)})})
        }
    }, self.scope))

    return Ast.TopNode(Ast.Block({
        Ast.ReturnStatement{Ast.FunctionCallExpression(functionNode, {
            Ast.OrExpression(Ast.AndExpression(Ast.VariableExpression(newGlobalScope, getfenvVar), Ast.FunctionCallExpression(Ast.VariableExpression(newGlobalScope, getfenvVar), {})), Ast.VariableExpression(newGlobalScope, envVar)),
            Ast.OrExpression(Ast.VariableExpression(newGlobalScope, unpackVar), Ast.IndexExpression(Ast.VariableExpression(newGlobalScope, tableVar), Ast.StringExpression("unpack"))),
            Ast.VariableExpression(newGlobalScope, setmetaVar),
            Ast.VariableExpression(newGlobalScope, selectVar),
            Ast.TableConstructorExpression({Ast.TableEntry(Ast.VarargExpression())}),
        })}
    }, psc), newGlobalScope)
end

function Compiler:getCreateClosureVar(argCount)
    if not self.createClosureVars[argCount] then
        local var = Ast.AssignmentVariable(self.scope, self.scope:addVariable())
        local cs  = Scope:new(self.scope)
        local css = Scope:new(cs)
        local posArg   = cs:addVariable(); local upvalsArg = cs:addVariable()
        local proxyObj = cs:addVariable(); local funcVar   = cs:addVariable()

        css:addReferenceToHigherScope(self.scope, self.containerFuncVar)
        css:addReferenceToHigherScope(cs, posArg)
        css:addReferenceToHigherScope(cs, upvalsArg, 1)
        cs:addReferenceToHigherScope(self.scope, self.upvaluesProxyFunctionVar)
        css:addReferenceToHigherScope(cs, proxyObj)

        local argsTb, argsTb2 = {}, {}
        for i = 1, argCount do
            local arg = css:addVariable()
            argsTb[i]  = Ast.VariableExpression(css, arg)
            argsTb2[i] = Ast.TableEntry(Ast.VariableExpression(css, arg))
        end

        self.createClosureVars[argCount] = { var=var, val=Ast.FunctionLiteralExpression({
            Ast.VariableExpression(cs, posArg), Ast.VariableExpression(cs, upvalsArg),
        }, Ast.Block({
            Ast.LocalVariableDeclaration(cs, {proxyObj}, {
                Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.upvaluesProxyFunctionVar), {Ast.VariableExpression(cs, upvalsArg)})
            }),
            Ast.LocalVariableDeclaration(cs, {funcVar}, {
                Ast.FunctionLiteralExpression(argsTb, Ast.Block({
                    Ast.ReturnStatement{Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.containerFuncVar), {
                        Ast.VariableExpression(cs, posArg),
                        Ast.TableConstructorExpression(argsTb2),
                        Ast.VariableExpression(cs, upvalsArg),
                        Ast.VariableExpression(cs, proxyObj),
                    })}
                }, css))
            }),
            Ast.ReturnStatement{Ast.VariableExpression(cs, funcVar)},
        }, cs)) }
    end
    local var = self.createClosureVars[argCount].var
    return var.scope, var.id
end

function Compiler:pushRegisterUsageInfo()
    table.insert(self.registerUsageStack, {usedRegisters=self.usedRegisters, registers=self.registers})
    self.usedRegisters=0; self.registers={}
end

function Compiler:popRegisterUsageInfo()
    local info = table.remove(self.registerUsageStack)
    self.usedRegisters=info.usedRegisters; self.registers=info.registers
end

function Compiler:createUpvaluesGcFunc()
    local s = Scope:new(self.scope)
    local selfVar=s:addVariable(); local itVar=s:addVariable(); local valVar=s:addVariable()
    local ws=Scope:new(s)
    ws:addReferenceToHigherScope(self.scope, self.upvaluesReferenceCountsTable, 3)
    ws:addReferenceToHigherScope(s, valVar, 3); ws:addReferenceToHigherScope(s, itVar, 3)
    local ifs=Scope:new(ws)
    ifs:addReferenceToHigherScope(self.scope, self.upvaluesReferenceCountsTable, 1)
    ifs:addReferenceToHigherScope(self.scope, self.upvaluesTable, 1)
    local RCT = self.upvaluesReferenceCountsTable; local UT = self.upvaluesTable
    return Ast.FunctionLiteralExpression({Ast.VariableExpression(s, selfVar)}, Ast.Block({
        Ast.LocalVariableDeclaration(s, {itVar,valVar}, {Ast.NumberExpression(1), Ast.IndexExpression(Ast.VariableExpression(s, selfVar), Ast.NumberExpression(1))}),
        Ast.WhileStatement(Ast.Block({
            Ast.AssignmentStatement({
                Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, RCT), Ast.VariableExpression(s, valVar)),
                Ast.AssignmentVariable(s, itVar),
            },{
                Ast.SubExpression(Ast.IndexExpression(Ast.VariableExpression(self.scope, RCT), Ast.VariableExpression(s, valVar)), Ast.NumberExpression(1)),
                Ast.AddExpression(unpack(util.shuffle{Ast.VariableExpression(s, itVar), Ast.NumberExpression(1)})),
            }),
            Ast.IfStatement(Ast.EqualsExpression(unpack(util.shuffle{Ast.IndexExpression(Ast.VariableExpression(self.scope, RCT), Ast.VariableExpression(s, valVar)), Ast.NumberExpression(0)})), Ast.Block({
                Ast.AssignmentStatement({
                    Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, RCT), Ast.VariableExpression(s, valVar)),
                    Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, UT), Ast.VariableExpression(s, valVar)),
                },{Ast.NilExpression(), Ast.NilExpression()})
            }, ifs),{},nil),
            Ast.AssignmentStatement({Ast.AssignmentVariable(s, valVar)},{Ast.IndexExpression(Ast.VariableExpression(s, selfVar), Ast.VariableExpression(s, itVar))}),
        }, ws), Ast.VariableExpression(s, valVar), s)
    }, s))
end

function Compiler:createFreeUpvalueFunc()
    local s=Scope:new(self.scope); local argV=s:addVariable()
    local ifs=Scope:new(s)
    ifs:addReferenceToHigherScope(s, argV, 3)
    s:addReferenceToHigherScope(self.scope, self.upvaluesReferenceCountsTable, 2)
    local RCT=self.upvaluesReferenceCountsTable; local UT=self.upvaluesTable
    return Ast.FunctionLiteralExpression({Ast.VariableExpression(s, argV)}, Ast.Block({
        Ast.AssignmentStatement({Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, RCT), Ast.VariableExpression(s, argV))},{
            Ast.SubExpression(Ast.IndexExpression(Ast.VariableExpression(self.scope, RCT), Ast.VariableExpression(s, argV)), Ast.NumberExpression(1))
        }),
        Ast.IfStatement(Ast.EqualsExpression(unpack(util.shuffle{Ast.IndexExpression(Ast.VariableExpression(self.scope, RCT), Ast.VariableExpression(s, argV)), Ast.NumberExpression(0)})), Ast.Block({
            Ast.AssignmentStatement({
                Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, RCT), Ast.VariableExpression(s, argV)),
                Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, UT), Ast.VariableExpression(s, argV)),
            },{Ast.NilExpression(), Ast.NilExpression()})
        }, ifs),{},nil)
    }, s))
end

function Compiler:createUpvaluesProxyFunc()
    local s=Scope:new(self.scope)
    local entriesV=s:addVariable()
    local fs=Scope:new(s); local fa=fs:addVariable()
    fs:addReferenceToHigherScope(self.scope, self.upvaluesReferenceCountsTable, 2)
    fs:addReferenceToHigherScope(s, entriesV, 2)
    s:addReferenceToHigherScope(self.scope, self.setmetatableVar)
    s:addReferenceToHigherScope(self.scope, self.upvaluesGcFunctionVar)
    local RCT=self.upvaluesReferenceCountsTable; local gcF=self.upvaluesGcFunctionVar
    local lenRet=self.upvalsProxyLenReturn
    local retScope=Scope:new(s)
    return Ast.FunctionLiteralExpression({Ast.VariableExpression(s, entriesV)}, Ast.Block({
        Ast.ForStatement(fs, fa, Ast.NumberExpression(1), Ast.LenExpression(Ast.VariableExpression(s, entriesV)), Ast.NumberExpression(1), Ast.Block({
            Ast.AssignmentStatement({Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, RCT), Ast.IndexExpression(Ast.VariableExpression(s, entriesV), Ast.VariableExpression(fs, fa)))},{
                Ast.AddExpression(unpack(util.shuffle{
                    Ast.IndexExpression(Ast.VariableExpression(self.scope, RCT), Ast.IndexExpression(Ast.VariableExpression(s, entriesV), Ast.VariableExpression(fs, fa))),
                    Ast.NumberExpression(1),
                }))
            })
        }, fs), s),
        Ast.ReturnStatement({Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.setmetatableVar), {
            Ast.TableConstructorExpression({}),
            Ast.TableConstructorExpression({
                Ast.KeyedTableEntry(Ast.StringExpression("__gc"),    Ast.VariableExpression(self.scope, gcF)),
                Ast.KeyedTableEntry(Ast.StringExpression("__index"), Ast.VariableExpression(s, entriesV)),
                Ast.KeyedTableEntry(Ast.StringExpression("__len"),   Ast.FunctionLiteralExpression({}, Ast.Block({Ast.ReturnStatement({Ast.NumberExpression(lenRet)})}, retScope))),
            })
        })})
    }, s))
end

function Compiler:createAllocUpvalFunction()
    local s=Scope:new(self.scope)
    s:addReferenceToHigherScope(self.scope, self.currentUpvalId, 4)
    s:addReferenceToHigherScope(self.scope, self.upvaluesReferenceCountsTable, 1)
    return Ast.FunctionLiteralExpression({}, Ast.Block({
        Ast.AssignmentStatement({Ast.AssignmentVariable(self.scope, self.currentUpvalId)},{
            Ast.AddExpression(unpack(util.shuffle({Ast.VariableExpression(self.scope, self.currentUpvalId), Ast.NumberExpression(1)})))
        }),
        Ast.AssignmentStatement({Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, self.upvaluesReferenceCountsTable), Ast.VariableExpression(self.scope, self.currentUpvalId))},{Ast.NumberExpression(1)}),
        Ast.ReturnStatement({Ast.VariableExpression(self.scope, self.currentUpvalId)}),
    }, s))
end

function Compiler:emitContainerFuncBody()
    util.shuffle(self.blocks)

    local blocks = {}
    for _, block in ipairs(self.blocks) do
        local bstats = block.statements
        for i = 2, #bstats do
            local stat=bstats[i]; local reads=stat.reads; local writes=stat.writes
            local maxShift=0; local usesUpvals=stat.usesUpvals
            for shift=1, i-1 do
                local s2=bstats[i-shift]
                if s2.usesUpvals and usesUpvals then break end
                local f=true
                for r in pairs(s2.reads)  do if writes[r]  then f=false; break end end
                if f then for r in pairs(s2.writes) do if writes[r] or reads[r] then f=false; break end end end
                if not f then break end
                maxShift=shift
            end
            local shift=math.random(0, maxShift)
            for j=1, shift do bstats[i-j], bstats[i-j+1] = bstats[i-j+1], bstats[i-j] end
        end
        local stats={}
        for _, s in ipairs(block.statements) do table.insert(stats, s.statement) end
        table.insert(blocks, {id=block.id, block=Ast.Block(stats, block.scope)})
    end

    table.sort(blocks, function(a,b) return a.id < b.id end)

    local function buildIfBlock(scope, id, lBlock, rBlock)
        return Ast.Block({Ast.IfStatement(Ast.LessThanExpression(self:pos(scope), Ast.NumberExpression(id)), lBlock, {}, rBlock)}, scope)
    end

    local function buildWhileBody(tb, l, r, pScope, scope)
        local len = r-l+1
        if len==1 then tb[r].block.scope:setParent(pScope); return tb[r].block end
        if len==0 then return nil end
        local mid=l+math.ceil(len/2)
        local bound=math.random(tb[mid-1].id, tb[mid].id)
        local ifs=scope or Scope:new(pScope)
        return buildIfBlock(ifs, bound, buildWhileBody(tb,l,mid-1,ifs), buildWhileBody(tb,mid,r,ifs))
    end

    local whileBody=buildWhileBody(blocks,1,#blocks,self.containerFuncScope,self.whileScope)
    self.whileScope:addReferenceToHigherScope(self.containerFuncScope, self.returnVar, 1)
    self.whileScope:addReferenceToHigherScope(self.containerFuncScope, self.posVar)
    self.containerFuncScope:addReferenceToHigherScope(self.scope, self.unpackVar)

    local decls={self.returnVar}
    for i, var in pairs(self.registerVars) do
        if i~=MAX_REGS then table.insert(decls, var) end
    end

    local stats={
        Ast.LocalVariableDeclaration(self.containerFuncScope, util.shuffle(decls), {}),
        Ast.WhileStatement(whileBody, Ast.VariableExpression(self.containerFuncScope, self.posVar)),
        Ast.AssignmentStatement({Ast.AssignmentVariable(self.containerFuncScope, self.posVar)},{
            Ast.LenExpression(Ast.VariableExpression(self.containerFuncScope, self.detectGcCollectVar))
        }),
        Ast.ReturnStatement{Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.unpackVar), {
            Ast.VariableExpression(self.containerFuncScope, self.returnVar)
        })},
    }
    if self.maxUsedRegister >= MAX_REGS then
        table.insert(stats,1,Ast.LocalVariableDeclaration(self.containerFuncScope,{self.registerVars[MAX_REGS]},{Ast.TableConstructorExpression({})}))
    end
    return Ast.Block(stats, self.containerFuncScope)
end

function Compiler:freeRegister(id, force)
    if force or not(self.registers[id]==self.VAR_REGISTER) then
        self.usedRegisters=self.usedRegisters-1; self.registers[id]=false
    end
end

function Compiler:isVarRegister(id) return self.registers[id]==self.VAR_REGISTER end

function Compiler:allocRegister(isVar)
    self.usedRegisters=self.usedRegisters+1
    if not isVar then
        if not self.registers[self.POS_REGISTER]    then self.registers[self.POS_REGISTER]=true;    return self.POS_REGISTER    end
        if not self.registers[self.RETURN_REGISTER] then self.registers[self.RETURN_REGISTER]=true; return self.RETURN_REGISTER end
    end
    local id=0
    if self.usedRegisters < MAX_REGS*MAX_REGS_MUL then
        repeat id=math.random(1,MAX_REGS-1) until not self.registers[id]
    else
        repeat id=id+1 until not self.registers[id]
    end
    if id>self.maxUsedRegister then self.maxUsedRegister=id end
    self.registers[id] = isVar and self.VAR_REGISTER or true
    return id
end

function Compiler:isUpvalue(scope,id)  return self.upvalVars[scope] and self.upvalVars[scope][id] end
function Compiler:makeUpvalue(scope,id) if not self.upvalVars[scope] then self.upvalVars[scope]={} end; self.upvalVars[scope][id]=true end

function Compiler:getVarRegister(scope, id, functionDepth, potentialId)
    if not self.registersForVar[scope] then self.registersForVar[scope]={}; self.scopeFunctionDepths[scope]=functionDepth end
    local reg=self.registersForVar[scope][id]
    if not reg then
        if potentialId and self.registers[potentialId]~=self.VAR_REGISTER and potentialId~=self.POS_REGISTER and potentialId~=self.RETURN_REGISTER then
            self.registers[potentialId]=self.VAR_REGISTER; reg=potentialId
        else reg=self:allocRegister(true) end
        self.registersForVar[scope][id]=reg
    end
    return reg
end

function Compiler:getRegisterVarId(id)
    if not self.registerVars[id] then self.registerVars[id]=self.containerFuncScope:addVariable() end
    return self.registerVars[id]
end

function Compiler:register(scope, id)
    if id==self.POS_REGISTER    then return self:pos(scope) end
    if id==self.RETURN_REGISTER then return self:getReturn(scope) end
    if id<MAX_REGS then
        local vid=self:getRegisterVarId(id); scope:addReferenceToHigherScope(self.containerFuncScope, vid)
        return Ast.VariableExpression(self.containerFuncScope, vid)
    end
    local vid=self:getRegisterVarId(MAX_REGS); scope:addReferenceToHigherScope(self.containerFuncScope, vid)
    return Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope, vid), Ast.NumberExpression((id-MAX_REGS)+1))
end

function Compiler:registerList(scope, ids)
    local l={} for i,id in ipairs(ids) do l[i]=self:register(scope,id) end return l
end

function Compiler:registerAssignment(scope, id)
    if id==self.POS_REGISTER    then return self:posAssignment(scope) end
    if id==self.RETURN_REGISTER then return self:returnAssignment(scope) end
    if id<MAX_REGS then
        local vid=self:getRegisterVarId(id); scope:addReferenceToHigherScope(self.containerFuncScope, vid)
        return Ast.AssignmentVariable(self.containerFuncScope, vid)
    end
    local vid=self:getRegisterVarId(MAX_REGS); scope:addReferenceToHigherScope(self.containerFuncScope, vid)
    return Ast.AssignmentIndexing(Ast.VariableExpression(self.containerFuncScope, vid), Ast.NumberExpression((id-MAX_REGS)+1))
end

function Compiler:setRegister(scope, id, val, compound)
    if compound then return compound(self:registerAssignment(scope,id), val) end
    return Ast.AssignmentStatement({self:registerAssignment(scope,id)},{val})
end

function Compiler:setRegisters(scope, ids, vals)
    local lhs={}; for i,id in ipairs(ids) do lhs[i]=self:registerAssignment(scope,id) end
    return Ast.AssignmentStatement(lhs, vals)
end

function Compiler:copyRegisters(scope, to, from)
    local lhs,vals={},{}
    for i,id in ipairs(to) do
        if from[i]~=id then table.insert(lhs,self:registerAssignment(scope,id)); table.insert(vals,self:register(scope,from[i])) end
    end
    if #lhs>0 then return Ast.AssignmentStatement(lhs,vals) end
end

function Compiler:resetRegisters() self.registers={} end
function Compiler:pos(scope)       scope:addReferenceToHigherScope(self.containerFuncScope, self.posVar); return Ast.VariableExpression(self.containerFuncScope, self.posVar) end
function Compiler:posAssignment(scope) scope:addReferenceToHigherScope(self.containerFuncScope, self.posVar); return Ast.AssignmentVariable(self.containerFuncScope, self.posVar) end
function Compiler:args(scope)      scope:addReferenceToHigherScope(self.containerFuncScope, self.argsVar); return Ast.VariableExpression(self.containerFuncScope, self.argsVar) end
function Compiler:unpack(scope)    scope:addReferenceToHigherScope(self.scope, self.unpackVar); return Ast.VariableExpression(self.scope, self.unpackVar) end
function Compiler:env(scope)       scope:addReferenceToHigherScope(self.scope, self.envVar); return Ast.VariableExpression(self.scope, self.envVar) end
function Compiler:jmp(scope, to)   scope:addReferenceToHigherScope(self.containerFuncScope, self.posVar); return Ast.AssignmentStatement({Ast.AssignmentVariable(self.containerFuncScope, self.posVar)},{to}) end
function Compiler:getReturn(scope) scope:addReferenceToHigherScope(self.containerFuncScope, self.returnVar); return Ast.VariableExpression(self.containerFuncScope, self.returnVar) end
function Compiler:returnAssignment(scope) scope:addReferenceToHigherScope(self.containerFuncScope, self.returnVar); return Ast.AssignmentVariable(self.containerFuncScope, self.returnVar) end

function Compiler:setPos(scope, val)
    scope:addReferenceToHigherScope(self.containerFuncScope, self.posVar)
    local v = val and Ast.NumberExpression(val) or Ast.IndexExpression(self:env(scope), randomStrings.randomStringNode(math.random(12,14)))
    return Ast.AssignmentStatement({Ast.AssignmentVariable(self.containerFuncScope, self.posVar)},{v})
end

function Compiler:setReturn(scope, val)
    scope:addReferenceToHigherScope(self.containerFuncScope, self.returnVar)
    return Ast.AssignmentStatement({Ast.AssignmentVariable(self.containerFuncScope, self.returnVar)},{val})
end

function Compiler:setUpvalueMember(scope, idExpr, valExpr, cc)
    scope:addReferenceToHigherScope(self.scope, self.upvaluesTable)
    if cc then return cc(Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, self.upvaluesTable), idExpr), valExpr) end
    return Ast.AssignmentStatement({Ast.AssignmentIndexing(Ast.VariableExpression(self.scope, self.upvaluesTable), idExpr)},{valExpr})
end

function Compiler:getUpvalueMember(scope, idExpr)
    scope:addReferenceToHigherScope(self.scope, self.upvaluesTable)
    return Ast.IndexExpression(Ast.VariableExpression(self.scope, self.upvaluesTable), idExpr)
end

function Compiler:compileTopNode(node)
    local startBlock=self:createBlock()
    self.startBlockId=startBlock.id; self:setActiveBlock(startBlock)
    local scope=startBlock.scope
    local varAccessLookup=lookupify{AstKind.AssignmentVariable,AstKind.VariableExpression,AstKind.FunctionDeclaration,AstKind.LocalFunctionDeclaration}
    visitast(node, function(node, data)
        if node.kind==AstKind.Block then node.scope.__depth=data.functionData.depth end
        if varAccessLookup[node.kind] and not node.scope.isGlobal and node.scope.__depth<data.functionData.depth then
            if not self:isUpvalue(node.scope, node.id) then self:makeUpvalue(node.scope, node.id) end
        end
    end, nil, nil)
    self.varargReg=self:allocRegister(true)
    scope:addReferenceToHigherScope(self.containerFuncScope, self.argsVar)
    scope:addReferenceToHigherScope(self.scope, self.selectVar)
    scope:addReferenceToHigherScope(self.scope, self.unpackVar)
    self:addStatement(self:setRegister(scope, self.varargReg, Ast.VariableExpression(self.containerFuncScope, self.argsVar)), {self.varargReg},{},false)
    self:compileBlock(node.body, 0)
    if self.activeBlock.advanceToNextBlock then
        self:addStatement(self:setPos(self.activeBlock.scope, nil),{self.POS_REGISTER},{},false)
        self:addStatement(self:setReturn(self.activeBlock.scope, Ast.TableConstructorExpression({})),{self.RETURN_REGISTER},{},false)
        self.activeBlock.advanceToNextBlock=false
    end
    self:resetRegisters()
end

function Compiler:compileFunction(node, funcDepth)
    funcDepth=funcDepth+1
    local oldActiveBlock=self.activeBlock
    local upperVarargReg=self.varargReg; self.varargReg=nil
    local upvalueExpressions,upvalueIds,usedRegs={},{},{}
    local oldGetUpvalueId=self.getUpvalueId
    self.getUpvalueId=function(self, scope, id)
        if not upvalueIds[scope] then upvalueIds[scope]={} end
        if upvalueIds[scope][id] then return upvalueIds[scope][id] end
        local sfd=self.scopeFunctionDepths[scope]; local expression
        if sfd==funcDepth then
            oldActiveBlock.scope:addReferenceToHigherScope(self.scope, self.allocUpvalFunction)
            expression=Ast.FunctionCallExpression(Ast.VariableExpression(self.scope, self.allocUpvalFunction),{})
        elseif sfd==funcDepth-1 then
            local varReg=self:getVarRegister(scope,id,sfd,nil)
            expression=self:register(oldActiveBlock.scope, varReg); table.insert(usedRegs, varReg)
        else
            local hid=oldGetUpvalueId(self,scope,id)
            oldActiveBlock.scope:addReferenceToHigherScope(self.containerFuncScope, self.currentUpvaluesVar)
            expression=Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope, self.currentUpvaluesVar), Ast.NumberExpression(hid))
        end
        table.insert(upvalueExpressions, Ast.TableEntry(expression))
        local uid=#upvalueExpressions; upvalueIds[scope][id]=uid; return uid
    end

    local block=self:createBlock(); self:setActiveBlock(block)
    local scope=self.activeBlock.scope; self:pushRegisterUsageInfo()
    for i,arg in ipairs(node.args) do
        if arg.kind==AstKind.VariableExpression then
            if self:isUpvalue(arg.scope, arg.id) then
                scope:addReferenceToHigherScope(self.scope, self.allocUpvalFunction)
                local argReg=self:getVarRegister(arg.scope, arg.id, funcDepth, nil)
                self:addStatement(self:setRegister(scope,argReg,Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.allocUpvalFunction),{})),{argReg},{},false)
                self:addStatement(self:setUpvalueMember(scope,self:register(scope,argReg),Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope,self.argsVar),Ast.NumberExpression(i))),{},{argReg},true)
            else
                local argReg=self:getVarRegister(arg.scope, arg.id, funcDepth, nil)
                scope:addReferenceToHigherScope(self.containerFuncScope, self.argsVar)
                self:addStatement(self:setRegister(scope,argReg,Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope,self.argsVar),Ast.NumberExpression(i))),{argReg},{},false)
            end
        else
            self.varargReg=self:allocRegister(true)
            scope:addReferenceToHigherScope(self.containerFuncScope, self.argsVar)
            scope:addReferenceToHigherScope(self.scope, self.selectVar)
            scope:addReferenceToHigherScope(self.scope, self.unpackVar)
            self:addStatement(self:setRegister(scope,self.varargReg,Ast.TableConstructorExpression({Ast.TableEntry(Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.selectVar),{Ast.NumberExpression(i),Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.unpackVar),{Ast.VariableExpression(self.containerFuncScope,self.argsVar)})}))})),{self.varargReg},{},false)
        end
    end
    self:compileBlock(node.body, funcDepth)
    if self.activeBlock.advanceToNextBlock then
        self:addStatement(self:setPos(self.activeBlock.scope,nil),{self.POS_REGISTER},{},false)
        self:addStatement(self:setReturn(self.activeBlock.scope,Ast.TableConstructorExpression({})),{self.RETURN_REGISTER},{},false)
        self.activeBlock.advanceToNextBlock=false
    end
    if self.varargReg then self:freeRegister(self.varargReg,true) end
    self.varargReg=upperVarargReg; self.getUpvalueId=oldGetUpvalueId
    self:popRegisterUsageInfo(); self:setActiveBlock(oldActiveBlock)
    local scope=self.activeBlock.scope
    local retReg=self:allocRegister(false)
    local isVararg=#node.args>0 and node.args[#node.args].kind==AstKind.VarargExpression
    local retrieveExpr
    if isVararg then
        scope:addReferenceToHigherScope(self.scope, self.createVarargClosureVar)
        retrieveExpr=Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.createVarargClosureVar),{Ast.NumberExpression(block.id),Ast.TableConstructorExpression(upvalueExpressions)})
    else
        local varScope,var=self:getCreateClosureVar(#node.args+math.random(0,5))
        scope:addReferenceToHigherScope(varScope, var)
        retrieveExpr=Ast.FunctionCallExpression(Ast.VariableExpression(varScope,var),{Ast.NumberExpression(block.id),Ast.TableConstructorExpression(upvalueExpressions)})
    end
    self:addStatement(self:setRegister(scope,retReg,retrieveExpr),{retReg},usedRegs,false)
    return retReg
end

function Compiler:compileBlock(block, funcDepth)
    for _,stat in ipairs(block.statements) do self:compileStatement(stat, funcDepth) end
    local scope=self.activeBlock.scope
    for id in ipairs(block.scope.variables) do
        local varReg=self:getVarRegister(block.scope, id, funcDepth, nil)
        if self:isUpvalue(block.scope, id) then
            scope:addReferenceToHigherScope(self.scope, self.freeUpvalueFunc)
            self:addStatement(self:setRegister(scope,varReg,Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.freeUpvalueFunc),{self:register(scope,varReg)})),{varReg},{varReg},false)
        else self:addStatement(self:setRegister(scope,varReg,Ast.NilExpression()),{varReg},{},false) end
        self:freeRegister(varReg, true)
    end
end

function Compiler:compileStatement(statement, funcDepth)
    local scope=self.activeBlock.scope

    if statement.kind==AstKind.ReturnStatement then
        local entries,regs={},{}
        for i,expr in ipairs(statement.args) do
            if i==#statement.args and (expr.kind==AstKind.FunctionCallExpression or expr.kind==AstKind.PassSelfFunctionCallExpression or expr.kind==AstKind.VarargExpression) then
                local reg=self:compileExpression(expr,funcDepth,self.RETURN_ALL)[1]
                table.insert(entries,Ast.TableEntry(Ast.FunctionCallExpression(self:unpack(scope),{self:register(scope,reg)}))); table.insert(regs,reg)
            else
                local reg=self:compileExpression(expr,funcDepth,1)[1]
                table.insert(entries,Ast.TableEntry(self:register(scope,reg))); table.insert(regs,reg)
            end
        end
        for _,reg in ipairs(regs) do self:freeRegister(reg,false) end
        self:addStatement(self:setReturn(scope,Ast.TableConstructorExpression(entries)),{self.RETURN_REGISTER},regs,false)
        self:addStatement(self:setPos(self.activeBlock.scope,nil),{self.POS_REGISTER},{},false)
        self.activeBlock.advanceToNextBlock=false; return
    end

    if statement.kind==AstKind.LocalVariableDeclaration then
        local exprregs={}
        for i,expr in ipairs(statement.expressions) do
            if i==#statement.expressions and #statement.ids>#statement.expressions then
                for _,reg in ipairs(self:compileExpression(expr,funcDepth,#statement.ids-#statement.expressions+1)) do table.insert(exprregs,reg) end
            elseif statement.ids[i] or expr.kind==AstKind.FunctionCallExpression or expr.kind==AstKind.PassSelfFunctionCallExpression then
                table.insert(exprregs, self:compileExpression(expr,funcDepth,1)[1])
            end
        end
        if #exprregs==0 then for i=1,#statement.ids do table.insert(exprregs,self:compileExpression(Ast.NilExpression(),funcDepth,1)[1]) end end
        for i,id in ipairs(statement.ids) do
            if exprregs[i] then
                if self:isUpvalue(statement.scope, id) then
                    local varReg=self:getVarRegister(statement.scope,id,funcDepth,nil)
                    scope:addReferenceToHigherScope(self.scope, self.allocUpvalFunction)
                    self:addStatement(self:setRegister(scope,varReg,Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.allocUpvalFunction),{})),{varReg},{},false)
                    self:addStatement(self:setUpvalueMember(scope,self:register(scope,varReg),self:register(scope,exprregs[i])),{},{varReg,exprregs[i]},true)
                    self:freeRegister(exprregs[i],false)
                else
                    local varreg=self:getVarRegister(statement.scope,id,funcDepth,exprregs[i])
                    self:addStatement(self:copyRegisters(scope,{varreg},{exprregs[i]}),{varreg},{exprregs[i]},false)
                    self:freeRegister(exprregs[i],false)
                end
            end
        end
        if not self.scopeFunctionDepths[statement.scope] then self.scopeFunctionDepths[statement.scope]=funcDepth end
        return
    end

    if statement.kind==AstKind.FunctionCallStatement then
        local baseReg=self:compileExpression(statement.base,funcDepth,1)[1]
        local retReg=self:allocRegister(false); local regs,args={},{}
        for i,expr in ipairs(statement.args) do
            if i==#statement.args and (expr.kind==AstKind.FunctionCallExpression or expr.kind==AstKind.PassSelfFunctionCallExpression or expr.kind==AstKind.VarargExpression) then
                local reg=self:compileExpression(expr,funcDepth,self.RETURN_ALL)[1]
                table.insert(args,Ast.FunctionCallExpression(self:unpack(scope),{self:register(scope,reg)})); table.insert(regs,reg)
            else
                local reg=self:compileExpression(expr,funcDepth,1)[1]
                table.insert(args,self:register(scope,reg)); table.insert(regs,reg)
            end
        end
        self:addStatement(self:setRegister(scope,retReg,Ast.FunctionCallExpression(self:register(scope,baseReg),args)),{retReg},{baseReg,unpack(regs)},true)
        self:freeRegister(baseReg,false); self:freeRegister(retReg,false)
        for _,reg in ipairs(regs) do self:freeRegister(reg,false) end
        return
    end

    if statement.kind==AstKind.PassSelfFunctionCallStatement then
        local baseReg=self:compileExpression(statement.base,funcDepth,1)[1]
        local tmpReg=self:allocRegister(false)
        local args={self:register(scope,baseReg)}; local regs={baseReg}
        for i,expr in ipairs(statement.args) do
            if i==#statement.args and (expr.kind==AstKind.FunctionCallExpression or expr.kind==AstKind.PassSelfFunctionCallExpression or expr.kind==AstKind.VarargExpression) then
                local reg=self:compileExpression(expr,funcDepth,self.RETURN_ALL)[1]
                table.insert(args,Ast.FunctionCallExpression(self:unpack(scope),{self:register(scope,reg)})); table.insert(regs,reg)
            else
                local reg=self:compileExpression(expr,funcDepth,1)[1]
                table.insert(args,self:register(scope,reg)); table.insert(regs,reg)
            end
        end
        self:addStatement(self:setRegister(scope,tmpReg,Ast.StringExpression(statement.passSelfFunctionName)),{tmpReg},{},false)
        self:addStatement(self:setRegister(scope,tmpReg,Ast.IndexExpression(self:register(scope,baseReg),self:register(scope,tmpReg))),{tmpReg},{tmpReg,baseReg},false)
        self:addStatement(self:setRegister(scope,tmpReg,Ast.FunctionCallExpression(self:register(scope,tmpReg),args)),{tmpReg},{tmpReg,unpack(regs)},true)
        self:freeRegister(baseReg,false); self:freeRegister(tmpReg,false)
        for _,reg in ipairs(regs) do self:freeRegister(reg,false) end
        return
    end

    if statement.kind==AstKind.LocalFunctionDeclaration then
        if self:isUpvalue(statement.scope, statement.id) then
            local varReg=self:getVarRegister(statement.scope,statement.id,funcDepth,nil)
            scope:addReferenceToHigherScope(self.scope, self.allocUpvalFunction)
            self:addStatement(self:setRegister(scope,varReg,Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.allocUpvalFunction),{})),{varReg},{},false)
            local retReg=self:compileFunction(statement,funcDepth)
            self:addStatement(self:setUpvalueMember(scope,self:register(scope,varReg),self:register(scope,retReg)),{},{varReg,retReg},true)
            self:freeRegister(retReg,false)
        else
            local retReg=self:compileFunction(statement,funcDepth)
            local varReg=self:getVarRegister(statement.scope,statement.id,funcDepth,retReg)
            self:addStatement(self:copyRegisters(scope,{varReg},{retReg}),{varReg},{retReg},false)
            self:freeRegister(retReg,false)
        end
        return
    end

    if statement.kind==AstKind.FunctionDeclaration then
        local retReg=self:compileFunction(statement,funcDepth)
        if #statement.indices>0 then
            local tblReg
            if statement.scope.isGlobal then
                tblReg=self:allocRegister(false)
                self:addStatement(self:setRegister(scope,tblReg,Ast.StringExpression(statement.scope:getVariableName(statement.id))),{tblReg},{},false)
                self:addStatement(self:setRegister(scope,tblReg,Ast.IndexExpression(self:env(scope),self:register(scope,tblReg))),{tblReg},{tblReg},true)
            elseif self.scopeFunctionDepths[statement.scope]==funcDepth then
                if self:isUpvalue(statement.scope,statement.id) then
                    tblReg=self:allocRegister(false)
                    local reg=self:getVarRegister(statement.scope,statement.id,funcDepth)
                    self:addStatement(self:setRegister(scope,tblReg,self:getUpvalueMember(scope,self:register(scope,reg))),{tblReg},{reg},true)
                else tblReg=self:getVarRegister(statement.scope,statement.id,funcDepth,retReg) end
            else
                tblReg=self:allocRegister(false)
                local upvalId=self:getUpvalueId(statement.scope,statement.id)
                scope:addReferenceToHigherScope(self.containerFuncScope, self.currentUpvaluesVar)
                self:addStatement(self:setRegister(scope,tblReg,self:getUpvalueMember(scope,Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope,self.currentUpvaluesVar),Ast.NumberExpression(upvalId)))),{tblReg},{},true)
            end
            for i=1,#statement.indices-1 do
                local indexReg=self:compileExpression(Ast.StringExpression(statement.indices[i]),funcDepth,1)[1]
                local old=tblReg; tblReg=self:allocRegister(false)
                self:addStatement(self:setRegister(scope,tblReg,Ast.IndexExpression(self:register(scope,old),self:register(scope,indexReg))),{tblReg},{tblReg,indexReg},false)
                self:freeRegister(old,false); self:freeRegister(indexReg,false)
            end
            local indexReg=self:compileExpression(Ast.StringExpression(statement.indices[#statement.indices]),funcDepth,1)[1]
            self:addStatement(Ast.AssignmentStatement({Ast.AssignmentIndexing(self:register(scope,tblReg),self:register(scope,indexReg))},{self:register(scope,retReg)}),{},{tblReg,indexReg,retReg},true)
            self:freeRegister(indexReg,false); self:freeRegister(tblReg,false); self:freeRegister(retReg,false)
            return
        end
        if statement.scope.isGlobal then
            local tmpReg=self:allocRegister(false)
            self:addStatement(self:setRegister(scope,tmpReg,Ast.StringExpression(statement.scope:getVariableName(statement.id))),{tmpReg},{},false)
            self:addStatement(Ast.AssignmentStatement({Ast.AssignmentIndexing(self:env(scope),self:register(scope,tmpReg))},{self:register(scope,retReg)}),{},{tmpReg,retReg},true)
            self:freeRegister(tmpReg,false)
        elseif self.scopeFunctionDepths[statement.scope]==funcDepth then
            if self:isUpvalue(statement.scope,statement.id) then
                local reg=self:getVarRegister(statement.scope,statement.id,funcDepth)
                self:addStatement(self:setUpvalueMember(scope,self:register(scope,reg),self:register(scope,retReg)),{},{reg,retReg},true)
            else
                local reg=self:getVarRegister(statement.scope,statement.id,funcDepth,retReg)
                if reg~=retReg then self:addStatement(self:setRegister(scope,reg,self:register(scope,retReg)),{reg},{retReg},false) end
            end
        else
            local upvalId=self:getUpvalueId(statement.scope,statement.id)
            scope:addReferenceToHigherScope(self.containerFuncScope, self.currentUpvaluesVar)
            self:addStatement(self:setUpvalueMember(scope,Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope,self.currentUpvaluesVar),Ast.NumberExpression(upvalId)),self:register(scope,retReg)),{},{retReg},true)
        end
        self:freeRegister(retReg,false); return
    end

    if statement.kind==AstKind.AssignmentStatement then
        local exprregs,idxRegs={},{}
        for i,pexpr in ipairs(statement.lhs) do
            if pexpr.kind==AstKind.AssignmentIndexing then
                idxRegs[i]={base=self:compileExpression(pexpr.base,funcDepth,1)[1], index=self:compileExpression(pexpr.index,funcDepth,1)[1]}
            end
        end
        for i,expr in ipairs(statement.rhs) do
            if i==#statement.rhs and #statement.lhs>#statement.rhs then
                for _,reg in ipairs(self:compileExpression(expr,funcDepth,#statement.lhs-#statement.rhs+1)) do
                    if self:isVarRegister(reg) then local ro=reg; reg=self:allocRegister(false); self:addStatement(self:copyRegisters(scope,{reg},{ro}),{reg},{ro},false) end
                    table.insert(exprregs,reg)
                end
            elseif statement.lhs[i] or expr.kind==AstKind.FunctionCallExpression or expr.kind==AstKind.PassSelfFunctionCallExpression then
                local reg=self:compileExpression(expr,funcDepth,1)[1]
                if self:isVarRegister(reg) then local ro=reg; reg=self:allocRegister(false); self:addStatement(self:copyRegisters(scope,{reg},{ro}),{reg},{ro},false) end
                table.insert(exprregs,reg)
            end
        end
        for i,pexpr in ipairs(statement.lhs) do
            if pexpr.kind==AstKind.AssignmentVariable then
                if pexpr.scope.isGlobal then
                    local tmpReg=self:allocRegister(false)
                    self:addStatement(self:setRegister(scope,tmpReg,Ast.StringExpression(pexpr.scope:getVariableName(pexpr.id))),{tmpReg},{},false)
                    self:addStatement(Ast.AssignmentStatement({Ast.AssignmentIndexing(self:env(scope),self:register(scope,tmpReg))},{self:register(scope,exprregs[i])}),{},{tmpReg,exprregs[i]},true)
                    self:freeRegister(tmpReg,false)
                elseif self.scopeFunctionDepths[pexpr.scope]==funcDepth then
                    if self:isUpvalue(pexpr.scope,pexpr.id) then
                        local reg=self:getVarRegister(pexpr.scope,pexpr.id,funcDepth)
                        self:addStatement(self:setUpvalueMember(scope,self:register(scope,reg),self:register(scope,exprregs[i])),{},{reg,exprregs[i]},true)
                    else
                        local reg=self:getVarRegister(pexpr.scope,pexpr.id,funcDepth,exprregs[i])
                        if reg~=exprregs[i] then self:addStatement(self:setRegister(scope,reg,self:register(scope,exprregs[i])),{reg},{exprregs[i]},false) end
                    end
                else
                    local upvalId=self:getUpvalueId(pexpr.scope,pexpr.id)
                    scope:addReferenceToHigherScope(self.containerFuncScope, self.currentUpvaluesVar)
                    self:addStatement(self:setUpvalueMember(scope,Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope,self.currentUpvaluesVar),Ast.NumberExpression(upvalId)),self:register(scope,exprregs[i])),{},{exprregs[i]},true)
                end
            elseif pexpr.kind==AstKind.AssignmentIndexing then
                local br=idxRegs[i].base; local ir=idxRegs[i].index
                self:addStatement(Ast.AssignmentStatement({Ast.AssignmentIndexing(self:register(scope,br),self:register(scope,ir))},{self:register(scope,exprregs[i])}),{},{exprregs[i],br,ir},true)
                self:freeRegister(exprregs[i],false); self:freeRegister(br,false); self:freeRegister(ir,false)
            end
        end
        return
    end

    if statement.kind==AstKind.IfStatement then
        local condReg=self:compileExpression(statement.condition,funcDepth,1)[1]
        local finalBlock=self:createBlock()
        local nextBlock=((statement.elsebody or #statement.elseifs>0) and self:createBlock()) or finalBlock
        local innerBlock=self:createBlock()
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.OrExpression(Ast.AndExpression(self:register(scope,condReg),Ast.NumberExpression(innerBlock.id)),Ast.NumberExpression(nextBlock.id))),{self.POS_REGISTER},{condReg},false)
        self:freeRegister(condReg,false)
        self:setActiveBlock(innerBlock); scope=innerBlock.scope
        self:compileBlock(statement.body,funcDepth)
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.NumberExpression(finalBlock.id)),{self.POS_REGISTER},{},false)
        for i,eif in ipairs(statement.elseifs) do
            self:setActiveBlock(nextBlock); condReg=self:compileExpression(eif.condition,funcDepth,1)[1]
            local ib=self:createBlock()
            nextBlock=(statement.elsebody or i<#statement.elseifs) and self:createBlock() or finalBlock
            scope=self.activeBlock.scope
            self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.OrExpression(Ast.AndExpression(self:register(scope,condReg),Ast.NumberExpression(ib.id)),Ast.NumberExpression(nextBlock.id))),{self.POS_REGISTER},{condReg},false)
            self:freeRegister(condReg,false)
            self:setActiveBlock(ib); scope=ib.scope
            self:compileBlock(eif.body,funcDepth)
            self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.NumberExpression(finalBlock.id)),{self.POS_REGISTER},{},false)
        end
        if statement.elsebody then
            self:setActiveBlock(nextBlock)
            self:compileBlock(statement.elsebody,funcDepth)
            self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.NumberExpression(finalBlock.id)),{self.POS_REGISTER},{},false)
        end
        self:setActiveBlock(finalBlock); return
    end

    if statement.kind==AstKind.DoStatement then self:compileBlock(statement.body,funcDepth); return end

    if statement.kind==AstKind.WhileStatement then
        local innerBlock=self:createBlock(); local finalBlock=self:createBlock(); local checkBlock=self:createBlock()
        statement.__start_block=checkBlock; statement.__final_block=finalBlock
        self:addStatement(self:setPos(scope,checkBlock.id),{self.POS_REGISTER},{},false)
        self:setActiveBlock(checkBlock); scope=self.activeBlock.scope
        local condReg=self:compileExpression(statement.condition,funcDepth,1)[1]
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.OrExpression(Ast.AndExpression(self:register(scope,condReg),Ast.NumberExpression(innerBlock.id)),Ast.NumberExpression(finalBlock.id))),{self.POS_REGISTER},{condReg},false)
        self:freeRegister(condReg,false)
        self:setActiveBlock(innerBlock); scope=self.activeBlock.scope
        self:compileBlock(statement.body,funcDepth)
        self:addStatement(self:setPos(scope,checkBlock.id),{self.POS_REGISTER},{},false)
        self:setActiveBlock(finalBlock); return
    end

    if statement.kind==AstKind.RepeatStatement then
        local innerBlock=self:createBlock(); local finalBlock=self:createBlock(); local checkBlock=self:createBlock()
        statement.__start_block=checkBlock; statement.__final_block=finalBlock
        local condReg=self:compileExpression(statement.condition,funcDepth,1)[1]
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.NumberExpression(innerBlock.id)),{self.POS_REGISTER},{},false)
        self:freeRegister(condReg,false)
        self:setActiveBlock(innerBlock); self:compileBlock(statement.body,funcDepth)
        scope=self.activeBlock.scope
        self:addStatement(self:setPos(scope,checkBlock.id),{self.POS_REGISTER},{},false)
        self:setActiveBlock(checkBlock); scope=self.activeBlock.scope
        local condReg2=self:compileExpression(statement.condition,funcDepth,1)[1]
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.OrExpression(Ast.AndExpression(self:register(scope,condReg2),Ast.NumberExpression(finalBlock.id)),Ast.NumberExpression(innerBlock.id))),{self.POS_REGISTER},{condReg2},false)
        self:freeRegister(condReg2,false); self:setActiveBlock(finalBlock); return
    end

    if statement.kind==AstKind.ForStatement then
        local checkBlock=self:createBlock(); local innerBlock=self:createBlock(); local finalBlock=self:createBlock()
        statement.__start_block=checkBlock; statement.__final_block=finalBlock
        local posState=self.registers[self.POS_REGISTER]; self.registers[self.POS_REGISTER]=self.VAR_REGISTER
        local initialReg=self:compileExpression(statement.initialValue,funcDepth,1)[1]
        local feReg=self:compileExpression(statement.finalValue,funcDepth,1)[1]
        local finalReg=self:allocRegister(false)
        self:addStatement(self:copyRegisters(scope,{finalReg},{feReg}),{finalReg},{feReg},false); self:freeRegister(feReg)
        local ieReg=self:compileExpression(statement.incrementBy,funcDepth,1)[1]
        local incReg=self:allocRegister(false)
        self:addStatement(self:copyRegisters(scope,{incReg},{ieReg}),{incReg},{ieReg},false); self:freeRegister(ieReg)
        local tmpReg=self:allocRegister(false)
        self:addStatement(self:setRegister(scope,tmpReg,Ast.NumberExpression(0)),{tmpReg},{},false)
        local incNegReg=self:allocRegister(false)
        self:addStatement(self:setRegister(scope,incNegReg,Ast.LessThanExpression(self:register(scope,incReg),self:register(scope,tmpReg))),{incNegReg},{incReg,tmpReg},false)
        self:freeRegister(tmpReg)
        local curReg=self:allocRegister(true)
        self:addStatement(self:setRegister(scope,curReg,Ast.SubExpression(self:register(scope,initialReg),self:register(scope,incReg))),{curReg},{initialReg,incReg},false)
        self:freeRegister(initialReg)
        self:addStatement(self:jmp(scope,Ast.NumberExpression(checkBlock.id)),{self.POS_REGISTER},{},false)
        self:setActiveBlock(checkBlock); scope=checkBlock.scope
        self:addStatement(self:setRegister(scope,curReg,Ast.AddExpression(self:register(scope,curReg),self:register(scope,incReg))),{curReg},{curReg,incReg},false)
        local t1=self:allocRegister(false); local t2=self:allocRegister(false)
        self:addStatement(self:setRegister(scope,t2,Ast.NotExpression(self:register(scope,incNegReg))),{t2},{incNegReg},false)
        self:addStatement(self:setRegister(scope,t1,Ast.LessThanOrEqualsExpression(self:register(scope,curReg),self:register(scope,finalReg))),{t1},{curReg,finalReg},false)
        self:addStatement(self:setRegister(scope,t1,Ast.AndExpression(self:register(scope,t2),self:register(scope,t1))),{t1},{t1,t2},false)
        self:addStatement(self:setRegister(scope,t2,Ast.GreaterThanOrEqualsExpression(self:register(scope,curReg),self:register(scope,finalReg))),{t2},{curReg,finalReg},false)
        self:addStatement(self:setRegister(scope,t2,Ast.AndExpression(self:register(scope,incNegReg),self:register(scope,t2))),{t2},{t2,incNegReg},false)
        self:addStatement(self:setRegister(scope,t1,Ast.OrExpression(self:register(scope,t2),self:register(scope,t1))),{t1},{t1,t2},false)
        self:freeRegister(t2)
        t2=self:compileExpression(Ast.NumberExpression(innerBlock.id),funcDepth,1)[1]
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.AndExpression(self:register(scope,t1),self:register(scope,t2))),{self.POS_REGISTER},{t1,t2},false)
        self:freeRegister(t2); self:freeRegister(t1)
        t2=self:compileExpression(Ast.NumberExpression(finalBlock.id),funcDepth,1)[1]
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.OrExpression(self:register(scope,self.POS_REGISTER),self:register(scope,t2))),{self.POS_REGISTER},{self.POS_REGISTER,t2},false)
        self:freeRegister(t2)
        self:setActiveBlock(innerBlock); scope=innerBlock.scope
        self.registers[self.POS_REGISTER]=posState
        local varReg=self:getVarRegister(statement.scope,statement.id,funcDepth,nil)
        if self:isUpvalue(statement.scope,statement.id) then
            scope:addReferenceToHigherScope(self.scope, self.allocUpvalFunction)
            self:addStatement(self:setRegister(scope,varReg,Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.allocUpvalFunction),{})),{varReg},{},false)
            self:addStatement(self:setUpvalueMember(scope,self:register(scope,varReg),self:register(scope,curReg)),{},{varReg,curReg},true)
        else self:addStatement(self:setRegister(scope,varReg,self:register(scope,curReg)),{varReg},{curReg},false) end
        self:compileBlock(statement.body,funcDepth)
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,Ast.NumberExpression(checkBlock.id)),{self.POS_REGISTER},{},false)
        self.registers[self.POS_REGISTER]=self.VAR_REGISTER
        self:freeRegister(finalReg); self:freeRegister(incNegReg); self:freeRegister(incReg); self:freeRegister(curReg,true)
        self.registers[self.POS_REGISTER]=posState; self:setActiveBlock(finalBlock); return
    end

    if statement.kind==AstKind.ForInStatement then
        local exprregs={}; local el=#statement.expressions
        for i,expr in ipairs(statement.expressions) do
            if i==el and el<3 then
                for j=1,4-el do table.insert(exprregs,(self:compileExpression(expr,funcDepth,4-el))[j]) end
            elseif i<=3 then table.insert(exprregs,self:compileExpression(expr,funcDepth,1)[1])
            else self:freeRegister(self:compileExpression(expr,funcDepth,1)[1],false) end
        end
        for i,reg in ipairs(exprregs) do
            if reg and self.registers[reg]~=self.VAR_REGISTER and reg~=self.POS_REGISTER and reg~=self.RETURN_REGISTER then
                self.registers[reg]=self.VAR_REGISTER
            else
                exprregs[i]=self:allocRegister(true)
                self:addStatement(self:copyRegisters(scope,{exprregs[i]},{reg}),{exprregs[i]},{reg},false)
            end
        end
        local checkBlock=self:createBlock(); local bodyBlock=self:createBlock(); local finalBlock=self:createBlock()
        statement.__start_block=checkBlock; statement.__final_block=finalBlock
        self:addStatement(self:setPos(scope,checkBlock.id),{self.POS_REGISTER},{},false)
        self:setActiveBlock(checkBlock); scope=self.activeBlock.scope
        local varRegs={}
        for i,id in ipairs(statement.ids) do varRegs[i]=self:getVarRegister(statement.scope,id,funcDepth) end
        self:addStatement(Ast.AssignmentStatement({
            self:registerAssignment(scope,exprregs[3]),
            varRegs[2] and self:registerAssignment(scope,varRegs[2]),
        },{Ast.FunctionCallExpression(self:register(scope,exprregs[1]),{self:register(scope,exprregs[2]),self:register(scope,exprregs[3])})}),{exprregs[3],varRegs[2]},{exprregs[1],exprregs[2],exprregs[3]},true)
        self:addStatement(Ast.AssignmentStatement({self:posAssignment(scope)},{Ast.OrExpression(Ast.AndExpression(self:register(scope,exprregs[3]),Ast.NumberExpression(bodyBlock.id)),Ast.NumberExpression(finalBlock.id))}),{self.POS_REGISTER},{exprregs[3]},false)
        self:setActiveBlock(bodyBlock); scope=self.activeBlock.scope
        self:addStatement(self:copyRegisters(scope,{varRegs[1]},{exprregs[3]}),{varRegs[1]},{exprregs[3]},false)
        for i=3,#varRegs do self:addStatement(self:setRegister(scope,varRegs[i],Ast.NilExpression()),{varRegs[i]},{},false) end
        self:compileBlock(statement.body,funcDepth)
        self:addStatement(self:setPos(scope,checkBlock.id),{self.POS_REGISTER},{},false)
        self:setActiveBlock(finalBlock)
        for _,reg in ipairs(exprregs) do self:freeRegister(reg,true) end
        return
    end

    if statement.kind==AstKind.BreakStatement then
        local toFree={}; local ss
        repeat
            ss=ss and ss.parentScope or statement.scope
            for id in ipairs(ss.variables) do table.insert(toFree,{scope=ss,id=id}) end
        until ss==statement.loop.body.scope
        for _,var in pairs(toFree) do
            local varReg=self:getVarRegister(var.scope,var.id,nil,nil)
            if self:isUpvalue(var.scope,var.id) then
                scope:addReferenceToHigherScope(self.scope, self.freeUpvalueFunc)
                self:addStatement(self:setRegister(scope,varReg,Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.freeUpvalueFunc),{self:register(scope,varReg)})),{varReg},{varReg},false)
            else self:addStatement(self:setRegister(scope,varReg,Ast.NilExpression()),{varReg},{},false) end
        end
        self:addStatement(self:setPos(scope,statement.loop.__final_block.id),{self.POS_REGISTER},{},false)
        self.activeBlock.advanceToNextBlock=false; return
    end

    if statement.kind==AstKind.ContinueStatement then
        local toFree={}; local ss
        repeat
            ss=ss and ss.parentScope or statement.scope
            for id in pairs(ss.variables) do table.insert(toFree,{scope=ss,id=id}) end
        until ss==statement.loop.body.scope
        for _,var in ipairs(toFree) do
            local varReg=self:getVarRegister(var.scope,var.id,nil,nil)
            if self:isUpvalue(var.scope,var.id) then
                scope:addReferenceToHigherScope(self.scope, self.freeUpvalueFunc)
                self:addStatement(self:setRegister(scope,varReg,Ast.FunctionCallExpression(Ast.VariableExpression(self.scope,self.freeUpvalueFunc),{self:register(scope,varReg)})),{varReg},{varReg},false)
            else self:addStatement(self:setRegister(scope,varReg,Ast.NilExpression()),{varReg},{},false) end
        end
        self:addStatement(self:setPos(scope,statement.loop.__start_block.id),{self.POS_REGISTER},{},false)
        self.activeBlock.advanceToNextBlock=false; return
    end

    local compoundMap={
        [AstKind.CompoundAddStatement]=Ast.CompoundAddStatement, [AstKind.CompoundSubStatement]=Ast.CompoundSubStatement,
        [AstKind.CompoundMulStatement]=Ast.CompoundMulStatement, [AstKind.CompoundDivStatement]=Ast.CompoundDivStatement,
        [AstKind.CompoundModStatement]=Ast.CompoundModStatement, [AstKind.CompoundPowStatement]=Ast.CompoundPowStatement,
        [AstKind.CompoundConcatStatement]=Ast.CompoundConcatStatement,
    }
    if compoundMap[statement.kind] then
        local cc=compoundMap[statement.kind]
        if statement.lhs.kind==AstKind.AssignmentIndexing then
            local br=self:compileExpression(statement.lhs.base,funcDepth,1)[1]
            local ir=self:compileExpression(statement.lhs.index,funcDepth,1)[1]
            local vr=self:compileExpression(statement.rhs,funcDepth,1)[1]
            self:addStatement(cc(Ast.AssignmentIndexing(self:register(scope,br),self:register(scope,ir)),self:register(scope,vr)),{},{br,ir,vr},true)
        else
            local vr=self:compileExpression(statement.rhs,funcDepth,1)[1]; local pe=statement.lhs
            if pe.scope.isGlobal then
                local tr=self:allocRegister(false)
                self:addStatement(self:setRegister(scope,tr,Ast.StringExpression(pe.scope:getVariableName(pe.id))),{tr},{},false)
                self:addStatement(Ast.AssignmentStatement({Ast.AssignmentIndexing(self:env(scope),self:register(scope,tr))},{self:register(scope,vr)}),{},{tr,vr},true)
                self:freeRegister(tr,false)
            elseif self.scopeFunctionDepths[pe.scope]==funcDepth then
                if self:isUpvalue(pe.scope,pe.id) then
                    local reg=self:getVarRegister(pe.scope,pe.id,funcDepth)
                    self:addStatement(self:setUpvalueMember(scope,self:register(scope,reg),self:register(scope,vr),cc),{},{reg,vr},true)
                else
                    local reg=self:getVarRegister(pe.scope,pe.id,funcDepth,vr)
                    if reg~=vr then self:addStatement(self:setRegister(scope,reg,self:register(scope,vr),cc),{reg},{vr},false) end
                end
            else
                local uid=self:getUpvalueId(pe.scope,pe.id)
                scope:addReferenceToHigherScope(self.containerFuncScope, self.currentUpvaluesVar)
                self:addStatement(self:setUpvalueMember(scope,Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope,self.currentUpvaluesVar),Ast.NumberExpression(uid)),self:register(scope,vr),cc),{},{vr},true)
            end
        end
        return
    end

    logger:error(string.format("%s is not a compileable statement!", statement.kind))
end

function Compiler:compileExpression(expression, funcDepth, numReturns)
    local scope=self.activeBlock.scope

    local function nilPad(regs, first)
        for i=2,numReturns do regs[i]=self:allocRegister(); self:addStatement(self:setRegister(scope,regs[i],Ast.NilExpression()),{regs[i]},{},false) end
    end

    if expression.kind==AstKind.StringExpression then
        local regs={}; regs[1]=self:allocRegister()
        self:addStatement(self:setRegister(scope,regs[1],Ast.StringExpression(expression.value)),{regs[1]},{},false)
        nilPad(regs); return regs
    end

    if expression.kind==AstKind.NumberExpression then
        local regs={}; regs[1]=self:allocRegister()
        self:addStatement(self:setRegister(scope,regs[1],Ast.NumberExpression(expression.value)),{regs[1]},{},false)
        nilPad(regs); return regs
    end

    if expression.kind==AstKind.BooleanExpression then
        local regs={}; regs[1]=self:allocRegister()
        self:addStatement(self:setRegister(scope,regs[1],Ast.BooleanExpression(expression.value)),{regs[1]},{},false)
        nilPad(regs); return regs
    end

    if expression.kind==AstKind.NilExpression then
        local regs={}
        for i=1,numReturns do regs[i]=self:allocRegister(); self:addStatement(self:setRegister(scope,regs[i],Ast.NilExpression()),{regs[i]},{},false) end
        return regs
    end

    if expression.kind==AstKind.VariableExpression then
        local regs={}
        for i=1,numReturns do
            if i==1 then
                if expression.scope.isGlobal then
                    regs[i]=self:allocRegister(false); local tr=self:allocRegister(false)
                    self:addStatement(self:setRegister(scope,tr,Ast.StringExpression(expression.scope:getVariableName(expression.id))),{tr},{},false)
                    self:addStatement(self:setRegister(scope,regs[i],Ast.IndexExpression(self:env(scope),self:register(scope,tr))),{regs[i]},{tr},true)
                    self:freeRegister(tr,false)
                elseif self.scopeFunctionDepths[expression.scope]==funcDepth then
                    if self:isUpvalue(expression.scope,expression.id) then
                        local reg=self:allocRegister(false); local vr=self:getVarRegister(expression.scope,expression.id,funcDepth,nil)
                        self:addStatement(self:setRegister(scope,reg,self:getUpvalueMember(scope,self:register(scope,vr))),{reg},{vr},true)
                        regs[i]=reg
                    else regs[i]=self:getVarRegister(expression.scope,expression.id,funcDepth,nil) end
                else
                    local reg=self:allocRegister(false); local uid=self:getUpvalueId(expression.scope,expression.id)
                    scope:addReferenceToHigherScope(self.containerFuncScope, self.currentUpvaluesVar)
                    self:addStatement(self:setRegister(scope,reg,self:getUpvalueMember(scope,Ast.IndexExpression(Ast.VariableExpression(self.containerFuncScope,self.currentUpvaluesVar),Ast.NumberExpression(uid)))),{reg},{},true)
                    regs[i]=reg
                end
            else regs[i]=self:allocRegister(); self:addStatement(self:setRegister(scope,regs[i],Ast.NilExpression()),{regs[i]},{},false) end
        end
        return regs
    end

    if expression.kind==AstKind.FunctionCallExpression then
        local baseReg=self:compileExpression(expression.base,funcDepth,1)[1]
        local retRegs={}; local returnAll=numReturns==self.RETURN_ALL
        if returnAll then retRegs[1]=self:allocRegister(false)
        else for i=1,numReturns do retRegs[i]=self:allocRegister(false) end end
        local argRegs={}
        for _,expr in ipairs(expression.args) do table.insert(argRegs,self:compileExpression(expr,funcDepth,1)[1]) end
        if returnAll then
            self:addStatement(self:setRegister(scope,retRegs[1],Ast.TableConstructorExpression{Ast.TableEntry(Ast.FunctionCallExpression(self:register(scope,baseReg),self:registerList(scope,argRegs)))}),{retRegs[1]},{baseReg,unpack(argRegs)},true)
        elseif numReturns>1 then
            local tr=self:allocRegister(false)
            self:addStatement(self:setRegister(scope,tr,Ast.TableConstructorExpression{Ast.TableEntry(Ast.FunctionCallExpression(self:register(scope,baseReg),self:registerList(scope,argRegs)))}),{tr},{baseReg,unpack(argRegs)},true)
            for i,reg in ipairs(retRegs) do self:addStatement(self:setRegister(scope,reg,Ast.IndexExpression(self:register(scope,tr),Ast.NumberExpression(i))),{reg},{tr},false) end
            self:freeRegister(tr,false)
        else
            self:addStatement(self:setRegister(scope,retRegs[1],Ast.FunctionCallExpression(self:register(scope,baseReg),self:registerList(scope,argRegs))),{retRegs[1]},{baseReg,unpack(argRegs)},true)
        end
        self:freeRegister(baseReg,false); for _,reg in ipairs(argRegs) do self:freeRegister(reg,false) end
        return retRegs
    end

    if expression.kind==AstKind.PassSelfFunctionCallExpression then
        local baseReg=self:compileExpression(expression.base,funcDepth,1)[1]
        local retRegs={}; local returnAll=numReturns==self.RETURN_ALL
        if returnAll then retRegs[1]=self:allocRegister(false)
        else for i=1,numReturns do retRegs[i]=self:allocRegister(false) end end
        local args={self:register(scope,baseReg)}; local regs={baseReg}
        for i,expr in ipairs(expression.args) do
            if i==#expression.args and (expr.kind==AstKind.FunctionCallExpression or expr.kind==AstKind.PassSelfFunctionCallExpression or expr.kind==AstKind.VarargExpression) then
                local reg=self:compileExpression(expr,funcDepth,self.RETURN_ALL)[1]
                table.insert(args,Ast.FunctionCallExpression(self:unpack(scope),{self:register(scope,reg)})); table.insert(regs,reg)
            else
                local reg=self:compileExpression(expr,funcDepth,1)[1]
                table.insert(args,self:register(scope,reg)); table.insert(regs,reg)
            end
        end
        if returnAll or numReturns>1 then
            local tr=self:allocRegister(false)
            self:addStatement(self:setRegister(scope,tr,Ast.StringExpression(expression.passSelfFunctionName)),{tr},{},false)
            self:addStatement(self:setRegister(scope,tr,Ast.IndexExpression(self:register(scope,baseReg),self:register(scope,tr))),{tr},{baseReg,tr},false)
            if returnAll then
                self:addStatement(self:setRegister(scope,retRegs[1],Ast.TableConstructorExpression{Ast.TableEntry(Ast.FunctionCallExpression(self:register(scope,tr),args))}),{retRegs[1]},{baseReg,unpack(regs)},true)
            else
                self:addStatement(self:setRegister(scope,tr,Ast.TableConstructorExpression{Ast.TableEntry(Ast.FunctionCallExpression(self:register(scope,tr),args))}),{tr},{baseReg,unpack(regs)},true)
                for i,reg in ipairs(retRegs) do self:addStatement(self:setRegister(scope,reg,Ast.IndexExpression(self:register(scope,tr),Ast.NumberExpression(i))),{reg},{tr},false) end
            end
            self:freeRegister(tr,false)
        else
            local tr=retRegs[1] or self:allocRegister(false)
            self:addStatement(self:setRegister(scope,tr,Ast.StringExpression(expression.passSelfFunctionName)),{tr},{},false)
            self:addStatement(self:setRegister(scope,tr,Ast.IndexExpression(self:register(scope,baseReg),self:register(scope,tr))),{tr},{baseReg,tr},false)
            self:addStatement(self:setRegister(scope,retRegs[1],Ast.FunctionCallExpression(self:register(scope,tr),args)),{retRegs[1]},{baseReg,unpack(regs)},true)
        end
        self:freeRegister(baseReg,false); for _,reg in ipairs(regs) do self:freeRegister(reg,false) end
        return retRegs
    end

    if expression.kind==AstKind.IndexExpression then
        local regs={}; regs[1]=self:allocRegister()
        local br=self:compileExpression(expression.base,funcDepth,1)[1]
        local ir=self:compileExpression(expression.index,funcDepth,1)[1]
        self:addStatement(self:setRegister(scope,regs[1],Ast.IndexExpression(self:register(scope,br),self:register(scope,ir))),{regs[1]},{br,ir},true)
        self:freeRegister(br,false); self:freeRegister(ir,false)
        nilPad(regs); return regs
    end

    if self.BIN_OPS[expression.kind] then
        local regs={}; regs[1]=self:allocRegister()
        local lR=self:compileExpression(expression.lhs,funcDepth,1)[1]
        local rR=self:compileExpression(expression.rhs,funcDepth,1)[1]
        self:addStatement(self:setRegister(scope,regs[1],Ast[expression.kind](self:register(scope,lR),self:register(scope,rR))),{regs[1]},{lR,rR},true)
        self:freeRegister(rR,false); self:freeRegister(lR,false)
        nilPad(regs); return regs
    end

    for _,ekind in ipairs({AstKind.NotExpression, AstKind.NegateExpression, AstKind.LenExpression}) do
        if expression.kind==ekind then
            local regs={}; regs[1]=self:allocRegister()
            local rR=self:compileExpression(expression.rhs,funcDepth,1)[1]
            self:addStatement(self:setRegister(scope,regs[1],Ast[ekind](self:register(scope,rR))),{regs[1]},{rR},ekind~=AstKind.NotExpression)
            self:freeRegister(rR,false); nilPad(regs); return regs
        end
    end

    local function compileShortCircuit(isOr)
        local posState=self.registers[self.POS_REGISTER]; self.registers[self.POS_REGISTER]=self.VAR_REGISTER
        local regs={}
        for i=1,numReturns do regs[i]=self:allocRegister(); if i~=1 then self:addStatement(self:setRegister(scope,regs[i],Ast.NilExpression()),{regs[i]},{},false) end end
        local resReg=regs[1]; local tmpReg
        if posState then tmpReg=self:allocRegister(false); self:addStatement(self:copyRegisters(scope,{tmpReg},{self.POS_REGISTER}),{tmpReg},{self.POS_REGISTER},false) end
        local lR=self:compileExpression(expression.lhs,funcDepth,1)[1]
        if expression.rhs.isConstant then
            local rR=self:compileExpression(expression.rhs,funcDepth,1)[1]
            local node=isOr and Ast.OrExpression(self:register(scope,lR),self:register(scope,rR)) or Ast.AndExpression(self:register(scope,lR),self:register(scope,rR))
            self:addStatement(self:setRegister(scope,resReg,node),{resReg},{lR,rR},false)
            if tmpReg then self:freeRegister(tmpReg,false) end
            self:freeRegister(lR,false); self:freeRegister(rR,false); return regs
        end
        local b1,b2=self:createBlock(),self:createBlock()
        self:addStatement(self:copyRegisters(scope,{resReg},{lR}),{resReg},{lR},false)
        local jumpCond=isOr and Ast.OrExpression(Ast.AndExpression(self:register(scope,lR),Ast.NumberExpression(b2.id)),Ast.NumberExpression(b1.id))
                             or Ast.OrExpression(Ast.AndExpression(self:register(scope,lR),Ast.NumberExpression(b1.id)),Ast.NumberExpression(b2.id))
        self:addStatement(self:setRegister(scope,self.POS_REGISTER,jumpCond),{self.POS_REGISTER},{lR},false)
        self:freeRegister(lR,false)
        do
            self:setActiveBlock(b1); local s=b1.scope
            local rR=self:compileExpression(expression.rhs,funcDepth,1)[1]
            self:addStatement(self:copyRegisters(s,{resReg},{rR}),{resReg},{rR},false); self:freeRegister(rR,false)
            self:addStatement(self:setRegister(s,self.POS_REGISTER,Ast.NumberExpression(b2.id)),{self.POS_REGISTER},{},false)
        end
        self.registers[self.POS_REGISTER]=posState; self:setActiveBlock(b2); scope=b2.scope
        if tmpReg then self:addStatement(self:copyRegisters(scope,{self.POS_REGISTER},{tmpReg}),{self.POS_REGISTER},{tmpReg},false); self:freeRegister(tmpReg,false) end
        return regs
    end

    if expression.kind==AstKind.OrExpression  then return compileShortCircuit(true)  end
    if expression.kind==AstKind.AndExpression then return compileShortCircuit(false) end

    if expression.kind==AstKind.TableConstructorExpression then
        local regs={}; regs[1]=self:allocRegister()
        local entries,entryRegs={},{}
        for i,entry in ipairs(expression.entries) do
            if entry.kind==AstKind.TableEntry then
                local val=entry.value
                if i==#expression.entries and (val.kind==AstKind.FunctionCallExpression or val.kind==AstKind.PassSelfFunctionCallExpression or val.kind==AstKind.VarargExpression) then
                    local reg=self:compileExpression(val,funcDepth,self.RETURN_ALL)[1]
                    table.insert(entries,Ast.TableEntry(Ast.FunctionCallExpression(self:unpack(scope),{self:register(scope,reg)}))); table.insert(entryRegs,reg)
                else
                    local reg=self:compileExpression(val,funcDepth,1)[1]
                    table.insert(entries,Ast.TableEntry(self:register(scope,reg))); table.insert(entryRegs,reg)
                end
            else
                local kr=self:compileExpression(entry.key,funcDepth,1)[1]; local vr=self:compileExpression(entry.value,funcDepth,1)[1]
                table.insert(entries,Ast.KeyedTableEntry(self:register(scope,kr),self:register(scope,vr)))
                table.insert(entryRegs,vr); table.insert(entryRegs,kr)
            end
        end
        self:addStatement(self:setRegister(scope,regs[1],Ast.TableConstructorExpression(entries)),{regs[1]},entryRegs,false)
        for _,reg in ipairs(entryRegs) do self:freeRegister(reg,false) end
        nilPad(regs); return regs
    end

    if expression.kind==AstKind.FunctionLiteralExpression then
        local regs={}; regs[1]=self:compileFunction(expression,funcDepth)
        nilPad(regs); return regs
    end

    if expression.kind==AstKind.VarargExpression then
        if numReturns==self.RETURN_ALL then return {self.varargReg} end
        local regs={}
        for i=1,numReturns do
            regs[i]=self:allocRegister(false)
            self:addStatement(self:setRegister(scope,regs[i],Ast.IndexExpression(self:register(scope,self.varargReg),Ast.NumberExpression(i))),{regs[i]},{self.varargReg},false)
        end
        return regs
    end

    logger:error(string.format("%s is not a compileable expression!", expression.kind))
end

return Compiler
