#!/usr/bin/ruby

class I_VM 
  attr_accessor :valstack, :valstack_top, :valstack_base, :ret, :callstack
  def initialize()
    @valstack = []
    @valstack_top = 0
    @valstack_base = 0
    @ret = nil
    @callstack = []
  end
end

i_valstack = []
i_callstack = []

class I_CON
  attr_accessor :tag, :args, :app, :ev
  def initialize(tag,args,app,ev)
    @tag = tag
    @args = args
    @app = app
    @ev = ev
  end
end

def i_SCHED(vm)
  $i_vm = vm
  $i_valstack = vm.valstack
  $i_valstack_top = vm.valstack_top
  $i_valstack_base = vm.valstack_base
  $i_ret = vm.ret
  $i_callstack = vm.callstack
end

def i_SLIDE(args)
  for i in 0 ... args
    $i_valstack[$i_valstack_base + i] = $i_valstack[$i_valstack_top + i]
  end
end

def i_PROJECT(val,loc,arity)
  for i in 0 ... arity
    $i_valstack[$i_valstack_base + i + loc] = val.args[i]
  end
end

def i_CALL(fun,args)
   $i_callstack.push(args)
   $i_callstack.push(fun)
 end

def i_ffiWrap(fid,oldbase,myoldbase)
  return Proc.new do |*arguments|
    $i_callstack = []
    $i_valstack = []
    res = fid
    arguments.each do |arg|
      if res.instance_of?(I_CON) then
        $i_valstack_top += 1
        $i_valstack[$i_valstack_top] = res
        $i_valstack[$i_valstack_top + 1] = arg
        i_SLIDE(2)
        $i_valstack_top = $i_valstack_base + 2
        i_CALL($_idris__123_APPLY0_125_,[oldbase])
        while $i_callstack.length > 0 do
          func = $i_callstack.pop()
          args = $i_callstack.pop()
          func.call(*args)
        end
        res = $i_ret
      end
    end
    $i_callstack = $i_vm.callstack
    $i_valstack = $i_vm.valstack
    $i_ret
  end
end


def i_charCode(s)
  s.class == String ? s.ord : s[0]
end

def i_fromCharCode(c)
  c.class == String ? c : c.chr  
end

def i_systemInfo()
  "Ruby #{RUBY_VERSION} [#{RUBY_PLATFORM}]" 
end




