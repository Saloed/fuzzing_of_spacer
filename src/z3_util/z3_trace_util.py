import errno
import fcntl
import io
import os
import threading
from typing import List

use_pipe = True


class Z3TraceUtil:
    def reset(self):
        pass

    def read_lines(self) -> List[str]:
        pass


Z3TraceManager: Z3TraceUtil

if not use_pipe:
    class FileBasedTraceManager(Z3TraceUtil):
        def __init__(self):
            self.offset = 0
            self.file = open('.z3-trace', 'r')

        def reset(self):
            self.offset = self.file.seek(0, io.SEEK_END)

        def read_lines(self) -> List[str]:
            self.file.seek(self.offset)
            lines = self.file.readlines()
            return lines


    Z3TraceManager = FileBasedTraceManager

else:

    def _setup_trace_pipe():
        if os.path.exists('.z3-trace'):
            os.remove('.z3-trace')
        os.mkfifo('.z3-trace')

        def open_pipe():
            global pipe
            pipe = os.open('.z3-trace', os.O_RDONLY | os.O_NONBLOCK)
            fcntl.fcntl(pipe, fcntl.F_SETPIPE_SZ, 2 ** 20)

        pipe_open_background = threading.Thread(target=open_pipe)
        pipe_open_background.start()

        # noinspection PyUnresolvedReferences
        import z3

        pipe_open_background.join()
        return pipe


    def _read_pipe_up_to_end(pipe, buffer: list):
        buffer_chunk_size = 65535
        try:
            while True:
                chunk = os.read(pipe, buffer_chunk_size)
                if not chunk:
                    break
                buffer.append(chunk)
        except OSError as ex:
            if ex.errno != errno.EAGAIN:
                raise ex


    def _read_all_timed_action(pipe, buffer: list, lock: threading.Lock):
        def read_loop():
            stopped = threading.Event()
            while not stopped.wait(10.0):
                with lock:
                    _read_pipe_up_to_end(pipe, buffer)

        runner = threading.Thread(target=read_loop)
        runner.daemon = True
        return runner


    pipe_descriptor = _setup_trace_pipe()


    class PipeBasedTraceManager(Z3TraceUtil):
        def __init__(self):
            self.pipe = pipe_descriptor
            self.lock = threading.Lock()
            self.buffer = list()
            self.scheduled_read = _read_all_timed_action(self.pipe, self.buffer, self.lock)
            self.scheduled_read.start()

        def reset(self):
            with self.lock:
                _read_pipe_up_to_end(self.pipe, self.buffer)
                self.buffer.clear()

        def read_lines(self) -> List[str]:
            with self.lock:
                _read_pipe_up_to_end(self.pipe, self.buffer)
                str_buffer = [it.decode('utf-8') for it in self.buffer]
                self.buffer.clear()
            return ''.join(str_buffer).split(os.linesep)


    Z3TraceManager = PipeBasedTraceManager
