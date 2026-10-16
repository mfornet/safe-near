(module
  (type (;0;) (func (param i32 i32)))
  (type (;1;) (func (param i32 i32) (result i32)))
  (type (;2;) (func))
  (type (;3;) (func (param i32 i32 i32)))
  (type (;4;) (func (param i32)))
  (import "stdio" "read" (func (;0;) (type 1)))
  (import "stdio" "write" (func (;1;) (type 0)))
  (import "talos" "oom" (func (;2;) (type 2)))
  (table (;0;) 2 2 funcref)
  (memory (;0;) 17)
  (global (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1048592)
  (global (;2;) i32 i32.const 1048585)
  (export "memory" (memory 0))
  (export "byte_echo" (func 3))
  (export "__heap_base" (global 1))
  (export "__data_end" (global 2))
  (elem (;0;) (i32.const 1) func 12)
  (func (;3;) (type 2)
    (local i32)
    call 4
    block ;; label = @1
      i32.const 1
      i32.const 1
      call 5
      local.tee 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 0
      i32.const 0
      i32.store8
      block ;; label = @2
        local.get 0
        i32.const 1
        call 8
        i32.const 1
        i32.ne
        br_if 0 (;@2;)
        local.get 0
        i32.const 1
        call 9
      end
      local.get 0
      i32.const 1
      i32.const 1
      call 7
      return
    end
    i32.const 1
    i32.const 1
    call 15
    unreachable
  )
  (func (;4;) (type 2)
    return
  )
  (func (;5;) (type 1) (param i32 i32) (result i32)
    (local i32 i32)
    block ;; label = @1
      block ;; label = @2
        local.get 1
        i32.const -1
        i32.add
        local.tee 2
        i32.const 0
        i32.load offset=1048576
        local.tee 3
        i32.const 1048592
        local.get 3
        select
        i32.add
        local.tee 3
        local.get 2
        i32.lt_u
        br_if 0 (;@2;)
        local.get 3
        i32.const 0
        local.get 1
        i32.sub
        i32.and
        local.tee 2
        local.get 0
        i32.add
        local.tee 1
        local.get 2
        i32.lt_u
        br_if 0 (;@2;)
        local.get 1
        i32.const 0
        i32.lt_s
        br_if 0 (;@2;)
        local.get 1
        i32.const 65535
        i32.add
        i32.const 16
        i32.shr_u
        local.tee 3
        memory.size
        local.tee 0
        i32.le_u
        br_if 1 (;@1;)
        local.get 3
        local.get 0
        i32.sub
        memory.grow
        i32.const -1
        i32.ne
        br_if 1 (;@1;)
      end
      call 6
      unreachable
    end
    i32.const 0
    local.get 1
    i32.store offset=1048576
    local.get 2
  )
  (func (;6;) (type 2)
    call 2
    unreachable
  )
  (func (;7;) (type 3) (param i32 i32 i32))
  (func (;8;) (type 1) (param i32 i32) (result i32)
    local.get 1
    local.get 0
    call 0
  )
  (func (;9;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call 1
  )
  (func (;10;) (type 4) (param i32)
    local.get 0
    call 11
    unreachable
  )
  (func (;11;) (type 4) (param i32)
    local.get 0
    i32.load
    local.get 0
    i32.load offset=4
    i32.const 0
    i32.load offset=1048580
    local.tee 0
    i32.const 1
    local.get 0
    select
    call_indirect (type 0)
    unreachable
  )
  (func (;12;) (type 0) (param i32 i32)
    i32.const 0
    i32.const 1
    i32.store8 offset=1048584
  )
  (func (;13;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call 14
    unreachable
  )
  (func (;14;) (type 0) (param i32 i32)
    (local i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 2
    global.set 0
    local.get 2
    local.get 1
    i32.store offset=12
    local.get 2
    local.get 0
    i32.store offset=8
    local.get 2
    i32.const 8
    i32.add
    call 10
    unreachable
  )
  (func (;15;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call 13
    unreachable
  )
)
