(module
  (type (;0;) (func (param i32 i32)))
  (type (;1;) (func (param i32 i32) (result i32)))
  (type (;2;) (func))
  (type (;3;) (func (param i64 i64) (result i64)))
  (type (;4;) (func (param i32 i32 i32)))
  (type (;5;) (func (param i32)))
  (import "stdio" "read" (func (;0;) (type 1)))
  (import "stdio" "write" (func (;1;) (type 0)))
  (import "talos" "oom" (func (;2;) (type 2)))
  (table (;0;) 2 2 funcref)
  (memory (;0;) 17)
  (global (;0;) (mut i32) i32.const 1048576)
  (global (;1;) i32 i32.const 1048592)
  (global (;2;) i32 i32.const 1048585)
  (export "memory" (memory 0))
  (export "gcd" (func 5))
  (export "__heap_base" (global 1))
  (export "__data_end" (global 2))
  (elem (;0;) (i32.const 1) func 14)
  (func (;3;) (type 2)
    (local i32 i32)
    global.get 0
    i32.const 16
    i32.sub
    local.tee 0
    global.set 0
    call 6
    block ;; label = @1
      i32.const 16
      i32.const 1
      call 9
      local.tee 1
      i32.eqz
      br_if 0 (;@1;)
      block ;; label = @2
        block ;; label = @3
          local.get 1
          i32.const 16
          call 10
          i32.const 16
          i32.ne
          br_if 0 (;@3;)
          local.get 0
          local.get 1
          i64.load align=1
          local.get 1
          i64.load offset=8 align=1
          call 4
          i64.store offset=8
          local.get 0
          i32.const 8
          i32.add
          i32.const 8
          call 11
          local.get 1
          i32.const 16
          i32.const 1
          call 8
          br 1 (;@2;)
        end
        local.get 1
        i32.const 16
        i32.const 1
        call 8
      end
      local.get 0
      i32.const 16
      i32.add
      global.set 0
      return
    end
    i32.const 1
    i32.const 16
    call 17
    unreachable
  )
  (func (;4;) (type 3) (param i64 i64) (result i64)
    (local i64)
    local.get 1
    local.get 0
    i64.or
    local.set 2
    block ;; label = @1
      local.get 0
      i64.eqz
      br_if 0 (;@1;)
      local.get 1
      i64.eqz
      br_if 0 (;@1;)
      local.get 2
      i64.ctz
      local.set 2
      block ;; label = @2
        local.get 0
        local.get 0
        i64.ctz
        i64.shr_u
        local.tee 0
        local.get 1
        local.get 1
        i64.ctz
        i64.shr_u
        local.tee 1
        i64.eq
        br_if 0 (;@2;)
        loop ;; label = @3
          block ;; label = @4
            local.get 0
            local.get 1
            i64.gt_u
            br_if 0 (;@4;)
            local.get 0
            local.get 1
            local.get 0
            i64.sub
            local.tee 1
            local.get 1
            i64.ctz
            i64.shr_u
            local.tee 1
            i64.eq
            br_if 2 (;@2;)
            br 1 (;@3;)
          end
          local.get 0
          local.get 1
          i64.sub
          local.tee 0
          local.get 0
          i64.ctz
          i64.shr_u
          local.tee 0
          local.get 1
          i64.ne
          br_if 0 (;@3;)
        end
        local.get 1
        local.set 0
      end
      local.get 0
      local.get 2
      i64.shl
      local.set 2
    end
    local.get 2
  )
  (func (;5;) (type 2)
    call 3
  )
  (func (;6;) (type 2)
    return
  )
  (func (;7;) (type 2)
    call 2
    unreachable
  )
  (func (;8;) (type 4) (param i32 i32 i32))
  (func (;9;) (type 1) (param i32 i32) (result i32)
    (local i32 i32)
    block ;; label = @1
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
      br_if 0 (;@1;)
      local.get 3
      i32.const 0
      local.get 1
      i32.sub
      i32.and
      local.tee 1
      local.get 0
      i32.add
      local.tee 2
      local.get 1
      i32.lt_u
      br_if 0 (;@1;)
      local.get 2
      i32.const 0
      i32.lt_s
      br_if 0 (;@1;)
      i32.const 0
      local.get 2
      i32.store offset=1048576
      block ;; label = @2
        local.get 1
        i32.eqz
        br_if 0 (;@2;)
        local.get 0
        i32.eqz
        br_if 0 (;@2;)
        local.get 1
        i32.const 0
        local.get 0
        memory.fill
      end
      local.get 1
      return
    end
    call 7
    unreachable
  )
  (func (;10;) (type 1) (param i32 i32) (result i32)
    local.get 1
    local.get 0
    call 0
  )
  (func (;11;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call 1
  )
  (func (;12;) (type 5) (param i32)
    local.get 0
    call 13
    unreachable
  )
  (func (;13;) (type 5) (param i32)
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
  (func (;14;) (type 0) (param i32 i32)
    i32.const 0
    i32.const 1
    i32.store8 offset=1048584
  )
  (func (;15;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call 16
    unreachable
  )
  (func (;16;) (type 0) (param i32 i32)
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
    call 12
    unreachable
  )
  (func (;17;) (type 0) (param i32 i32)
    local.get 1
    local.get 0
    call 15
    unreachable
  )
)
