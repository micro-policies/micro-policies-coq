extern int shared = 0;

void process1() {
  while (true) {
    shared += 1;
    yield();
  }
}

void process2() {
  while (true) {
    shared *= 2;
    yield();
  }
}

void scheduler() {
  void(*processes[2])() = {process1,process2};
  size_t next = 0;
  while (true) {
    processes()[next];
    // yield to here
    next = (next + 1) % (sizeof(processes) / sizeof(processes[0]));
  }
}
