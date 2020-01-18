use std::panic::catch_unwind;

use futures::executor::block_on;
use futures::pin_mut;
use futures::stream::TryStreamExt;

use mlua::{Error, Function, Lua, Result, Thread, ThreadStatus};

#[test]
fn test_thread() -> Result<()> {
    let lua = Lua::new();

    let thread = lua.create_thread(
        lua.load(
            r#"
            function (s)
                local sum = s
                for i = 1,4 do
                    sum = sum + coroutine.yield(sum)
                end
                return sum
            end
            "#,
        )
        .eval()?,
    )?;

    assert_eq!(thread.status(), ThreadStatus::Resumable);
    assert_eq!(thread.resume::<_, i64>(0)?, 0);
    assert_eq!(thread.status(), ThreadStatus::Resumable);
    assert_eq!(thread.resume::<_, i64>(1)?, 1);
    assert_eq!(thread.status(), ThreadStatus::Resumable);
    assert_eq!(thread.resume::<_, i64>(2)?, 3);
    assert_eq!(thread.status(), ThreadStatus::Resumable);
    assert_eq!(thread.resume::<_, i64>(3)?, 6);
    assert_eq!(thread.status(), ThreadStatus::Resumable);
    assert_eq!(thread.resume::<_, i64>(4)?, 10);
    assert_eq!(thread.status(), ThreadStatus::Unresumable);

    let accumulate = lua.create_thread(
        lua.load(
            r#"
            function (sum)
                while true do
                    sum = sum + coroutine.yield(sum)
                end
            end
            "#,
        )
        .eval::<Function>()?,
    )?;

    for i in 0..4 {
        accumulate.resume::<_, ()>(i)?;
    }
    assert_eq!(accumulate.resume::<_, i64>(4)?, 10);
    assert_eq!(accumulate.status(), ThreadStatus::Resumable);
    assert!(accumulate.resume::<_, ()>("error").is_err());
    assert_eq!(accumulate.status(), ThreadStatus::Error);

    let thread = lua
        .load(
            r#"
            coroutine.create(function ()
                while true do
                    coroutine.yield(42)
                end
            end)
        "#,
        )
        .eval::<Thread>()?;
    assert_eq!(thread.status(), ThreadStatus::Resumable);
    assert_eq!(thread.resume::<_, i64>(())?, 42);

    let thread: Thread = lua
        .load(
            r#"
            coroutine.create(function(arg)
                assert(arg == 42)
                local yieldarg = coroutine.yield(123)
                assert(yieldarg == 43)
                return 987
            end)
        "#,
        )
        .eval()?;

    assert_eq!(thread.resume::<_, u32>(42)?, 123);
    assert_eq!(thread.resume::<_, u32>(43)?, 987);

    match thread.resume::<_, u32>(()) {
        Err(Error::CoroutineInactive) => {}
        Err(_) => panic!("resuming dead coroutine error is not CoroutineInactive kind"),
        _ => panic!("resuming dead coroutine did not return error"),
    }

    Ok(())
}

#[test]
fn test_thread_stream() -> Result<()> {
    let lua = Lua::new();

    let thread = lua.create_thread(
        lua.load(
            r#"
            function (s)
                local sum = s
                for i = 1,10 do
                    sum = sum + i
                    coroutine.yield(sum)
                end
                return sum
            end
            "#,
        )
        .eval()?,
    )?;

    let result = block_on(async {
        let s = thread.into_stream(0);
        pin_mut!(s);
        let mut sum = 0;
        while let Some((lua, item)) = s.try_next().await? {
            let n: i64 = lua.unpack_multi(item)?;
            sum += n;
        }
        Ok::<_, Error>(sum)
    })?;

    assert_eq!(result, 275);

    Ok(())
}

#[test]
fn coroutine_from_closure() -> Result<()> {
    let lua = Lua::new();

    let thrd_main = lua.create_function(|_, ()| Ok(()))?;
    lua.globals().set("main", thrd_main)?;

    #[cfg(any(feature = "lua53", feature = "lua52", feature = "luajit"))]
    let thrd: Thread = lua.load("coroutine.create(main)").eval()?;
    #[cfg(feature = "lua51")]
    let thrd: Thread = lua
        .load("coroutine.create(function(...) return main(unpack(arg)) end)")
        .eval()?;

    thrd.resume::<_, ()>(())?;

    Ok(())
}

#[test]
fn coroutine_panic() {
    match catch_unwind(|| -> Result<()> {
        // check that coroutines propagate panics correctly
        let lua = Lua::new();
        let thrd_main = lua.create_function(|_, ()| -> Result<()> {
            panic!("test_panic");
        })?;
        lua.globals().set("main", thrd_main.clone())?;
        let thrd: Thread = lua.create_thread(thrd_main)?;
        thrd.resume(())
    }) {
        Ok(r) => panic!("coroutine panic not propagated, instead returned {:?}", r),
        Err(p) => assert!(*p.downcast::<&str>().unwrap() == "test_panic"),
    }
}

#[test]
fn test_thread_async() -> Result<()> {
    use std::time::Duration;

    let lua = Lua::new();

    use std::sync::Arc;

    let cnt = Arc::new(());
    let cnt2 = cnt.clone();
    let f = lua.create_async_function(move |_lua, ()| {
        let cnt3 = cnt2.clone();
        async move {
            println!("hello from async func");
            futures_timer::Delay::new(Duration::from_secs(1)).await;
            println!("sleep done");
            println!("[async] strong count: {}", Arc::strong_count(&cnt3));
            Ok(())
        }
    })?;

    let thread = lua.create_thread(f)?;

    block_on(async {
        let mut s = thread.into_stream(());
        let _ = s.try_next().await?;
        Ok::<_, Error>(())
    })?;

    lua.gc_collect()?;
    println!("cnt strong count: {}", Arc::strong_count(&cnt));

    Ok(())
}
