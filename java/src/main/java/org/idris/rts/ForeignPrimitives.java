package org.idris.rts;

import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.io.Closeable;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.InputStream;
import java.nio.ByteBuffer;
import java.nio.MappedByteBuffer;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.StandardOpenOption;
import java.nio.channels.Channel;
import java.nio.channels.Channels;
import java.nio.channels.FileChannel;
import static java.nio.channels.FileChannel.MapMode;
import java.nio.channels.SeekableByteChannel;
import java.nio.channels.ReadableByteChannel;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.Semaphore;

@SuppressWarnings("unchecked")
public class ForeignPrimitives {

    private static final Map<Thread, List<String>> args = new HashMap<>();
    private static final Semaphore messageMutex = new Semaphore(1);
    private static final Map<Thread, BlockingQueue<Object>> messages = new HashMap<>();
    private static final Set<Object> feofFiles = new HashSet<>();

    public static synchronized void idris_initArgs(Thread t, String[] args) {
        ForeignPrimitives.args.put(t, Arrays.asList(args));
    }

    public static synchronized int idris_numArgs(Object thread) {
        List<String> argsForThread = ForeignPrimitives.args.get((Thread) thread);
        return (argsForThread == null ? 0 : argsForThread.size());
    }

    public static synchronized String idris_getArg(Object thread, int num) {
        List<String> argsForThread = ForeignPrimitives.args.get((Thread) thread);
        return (argsForThread == null ? null : argsForThread.get(num));
    }

    public static String getenv(String x) {
        return System.getenv(x);
    }

    public static void exit(int exitCode) {
        System.exit(exitCode);
    }

    public static void usleep(int microsecs) {
        try {
            Thread.sleep(microsecs / 1000, microsecs % 1000);
        } catch (InterruptedException ex) {
        }
    }

    public static void idris_sendMessage(Object from, Object dest, Object message) throws InterruptedException {
        messageMutex.acquire();
        BlockingQueue<Object> messagesForTarget = messages.get((Thread) dest);
        if (messagesForTarget == null) {
            messagesForTarget = new LinkedBlockingQueue<>();
            messages.put((Thread) dest, messagesForTarget);
        }
        messagesForTarget.put(message);
        messageMutex.release();
    }

    public static int idris_checkMessage(Object dest) throws InterruptedException {
        messageMutex.acquire();
        BlockingQueue<Object> messagesForTarget = messages.get((Thread) dest);
        messageMutex.release();
        return (messagesForTarget == null ? 0 : messagesForTarget.size());
    }

    public static Object idris_recvMessage(Object dest) throws InterruptedException {
        messageMutex.acquire();
        BlockingQueue<Object> messagesForTarget = messages.get((Thread) dest);
        if (messagesForTarget == null) {
            messagesForTarget = new LinkedBlockingQueue();
            messages.put((Thread) dest, messagesForTarget);
        }
        messageMutex.release();
        return messagesForTarget.take();
    }

    public static void putStr(String str) {
        System.out.print(str);
    }

    public static void putchar(char c) {
        System.out.print(c);
    }

    public static int getchar() {
        try {
            return (char) System.in.read();
        } catch (IOException ex) {
            return -1;
        }
    }

    public static SeekableByteChannel fileOpen(String name, String privs) {
        try {
            OpenOption[] options;
            switch (privs) {
                case "r":
                    options = new StandardOpenOption[]{StandardOpenOption.READ};
                    break;
                case "r+":
                    options = new StandardOpenOption[]{StandardOpenOption.READ,
                        StandardOpenOption.WRITE};
                    break;
                case "w":
                    options = new StandardOpenOption[]{StandardOpenOption.WRITE,
                        StandardOpenOption.CREATE};
                    break;
                case "w+":
                    options = new StandardOpenOption[]{StandardOpenOption.READ,
                        StandardOpenOption.WRITE,
                        StandardOpenOption.CREATE};
                    break;
                case "a":
                    options = new StandardOpenOption[]{StandardOpenOption.WRITE,
                        StandardOpenOption.CREATE,
                        StandardOpenOption.APPEND};
                    break;
                case "a+":
                    options = new StandardOpenOption[]{StandardOpenOption.READ,
                        StandardOpenOption.WRITE,
                        StandardOpenOption.CREATE,
                        StandardOpenOption.APPEND};
                    break;
                default:
                    options = new StandardOpenOption[]{};
                    break;
            }
            return Files.newByteChannel(new File(name).toPath(), options);
        } catch (IOException ex) {
            return null;
        }
    }

    public static synchronized void fileClose(Object file) throws IOException {
        ((Closeable) file).close();
        feofFiles.remove(file);
    }

    public static void fputStr(Object file, String string) throws IOException {
        if (file instanceof PrintStream) {
            ((PrintStream) file).print(string);
        } else if (file instanceof SeekableByteChannel) {
            ((SeekableByteChannel) file).write(ByteBuffer.wrap(string.getBytes()));
        }
    }

    public static synchronized String idris_readStr(Object file) throws IOException {
        ReadableByteChannel channel = file instanceof InputStream
                ? Channels.newChannel((InputStream) file)
                : (ReadableByteChannel) file;
        ByteBuffer buf = ByteBuffer.allocate(1);
        StringBuilder resultBuilder = new StringBuilder("");
        String delimiter = System.getProperty("line.separator");
        int read = 0;
        do {
            buf.rewind();
            read = channel.read(buf);
            if (read > 0) {
                resultBuilder.append(new String(buf.array()));
                if (resultBuilder.lastIndexOf(delimiter) > -1) {
                    return resultBuilder.toString();
                }
            }
            if (read < 0) {
                feofFiles.add(file);
            }
        } while (read >= 0);
        return resultBuilder.toString();
    }

    public static int fileEOF(Object file) {
        return (feofFiles.contains(file) ? 1 : 0);
    }

    public static int isNull(Object o) {
        return (o == null ? 1 : 0);
    }

    public static Object malloc(int size) {
        return ByteBuffer.allocate(size);
    }

    public static void idris_memset(Object buf, int offset, Object c, int size) {
        ByteBuffer buffer = (ByteBuffer)buf;
        buffer.rewind();
        buffer.position(offset);
        byte init[] = new byte[size];
        Arrays.fill(init, (Byte)c);
        buffer.put(init, offset, size);
        buffer.rewind();
    }

    public static void free(Object buf) {
        buf = null;
    }

    public static byte idris_peek(Object buf, int offset) {
        ByteBuffer buffer = (ByteBuffer)buf;
        return buffer.get(offset);
    }

    public static void idris_poke(Object buf, int offset, Object data) {
        ByteBuffer buffer = (ByteBuffer)buf;
        buffer.put(offset, (Byte)data);
    }

    public static void idris_memmove(Object dstBuf, Object srcBuf, int dstOffset, int srcOffset, int size) {
        ByteBuffer dst = (ByteBuffer)dstBuf;
        ByteBuffer src = (ByteBuffer)srcBuf;
        byte [] srcData = new byte[size];
        src.rewind();
        src.position(srcOffset);
        src.get(srcData, 0, size);
        src.rewind();
        dst.rewind();
        dst.position(dstOffset);
        dst.put(srcData, 0, size);
        dst.rewind();
    }

    public static Integer idris_fileLength(Object handle) {
	try {
	    return handle instanceof InputStream
		    ? Integer.valueOf((int)((InputStream)handle).available())
		    : Integer.valueOf((int)((SeekableByteChannel)handle).size());
	} catch (IOException any) {
	    return -1;
	}
    }

    public static Object idris_mmap(Object handle, Integer can_write, int length) {
	Channel channel = handle instanceof InputStream
                ? Channels.newChannel((InputStream) handle)
                : (Channel) handle;
	if (!(channel instanceof FileChannel)) {
	    return null;
	}
	FileChannel fileChannel = (FileChannel)channel;
	MapMode mode = (can_write != 0 ? MapMode.PRIVATE : MapMode.READ_ONLY);
	try {
	    return fileChannel.map(mode, 0, length);
	} catch (Exception e) {
	    return null;
	}
    }

    public static Integer idris_munmap(Object buf, int length) {
	((MappedByteBuffer)buf).force();
	buf = null;
	return 0;
    }

    public final static Object idris_K(final Object result, final Object drop) {
        return result;
    }

    public final static Object idris_flipK(final Object drop, final Object result) {
        return result;
    }

    public final static Object idris_assignStack(final Object[] context, final int start, final Object... vars) {
        int i = start;
        for (Object var : vars) {
            context[i] = var;
        }
        return context;
    }

    public final static Object invokeOn(final Object obj, final String methodName, Object... args) throws NoSuchMethodException, IllegalAccessException, InvocationTargetException {
        Class cls = (obj instanceof Class ? (Class)obj : obj.getClass());
        Class argClasses[] = new Class[args.length];
        int i = 0;
        for (Object arg : args) {
            argClasses[i] = arg.getClass();
        }
        return cls.getMethod(methodName, argClasses).invoke(obj, args);
    }
    
    public final static Object newObject(final Object cls, Object... args) throws NoSuchMethodException, IllegalAccessException, InvocationTargetException, InstantiationException {
        Class clazz = (cls instanceof Class ? (Class)cls : cls.getClass());
        Class argClasses[] = new Class[args.length];
        int i = 0;
        for (Object arg : args) {
            argClasses[i] = arg.getClass();
        }
        return clazz.getConstructor(argClasses).newInstance(args);
    }
}
