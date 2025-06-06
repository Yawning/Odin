#+build haiku
package sys_haiku

import "base:intrinsics"
import "core:sys/posix"

foreign import libroot "system:c"

PATH_MAX   :: 1024
NAME_MAX   :: 256
MAXPATHLEN :: PATH_MAX

FILE_NAME_LENGTH :: NAME_MAX
PATH_NAME_LENGTH :: MAXPATHLEN
OS_NAME_LENGTH   :: 32

// Areas

area_info :: struct {
	area:       area_id,
	name:       [OS_NAME_LENGTH]byte,
	size:       uint,
	lock:       u32,
	protection: u32,
	team:       team_id,
	ram_size:   u32,
	copy_count: u32,
	in_count:   u32,
	out_count:  u32,
	address:    rawptr,
}

area_locking :: enum u32 {
	NO_LOCK            = 0,
	LAZY_LOCK          = 1,
	FULL_LOCK          = 2,
	CONTIGUOUS         = 3,
	LOMEM              = 4, // CONTIGUOUS, < 16 MB physical address
	_32_BIT_FULL_LOCK  = 5, // FULL_LOCK, < 4 GB physical addresses
	_32_BIT_CONTIGUOUS = 6, // CONTIGUOUS, < 4 GB physical address
}

// for create_area() and clone_area()
address_spec :: enum u32 {
	ANY_ADDRESS             = 0,
	EXACT_ADDRESS           = 1,
	BASE_ADDRESS            = 2,
	CLONE_ADDRESS           = 3,
	ANY_KERNEL_ADDRESS      = 4,
	// ANY_KERNEL_BLOCK_ADDRESS = 5,
	RANDOMIZED_ANY_ADDRESS  = 6,
	RANDOMIZED_BASE_ADDRESS = 7,
}

area_protection_flag :: enum u32 {
	READ_AREA      = 0,
	WRITE_AREA     = 1,
	EXECUTE_AREA   = 2,
	// "stack" protection is not available on most platforms - it's used
	// to only commit memory as needed, and have guard pages at the
	// bottom of the stack.
	STACK_AREA     = 3,
	CLONEABLE_AREA = 8,
}
area_protection_flags :: distinct bit_set[area_protection_flag; u32]

@(default_calling_convention="c")
foreign libroot {
	create_area         :: proc(name: cstring, startAddress: ^rawptr, addressSpec: address_spec, size: uint, lock: area_locking, protection: area_protection_flags) -> area_id ---
	clone_area          :: proc(name: cstring, destAddress: ^rawptr, addressSpec: address_spec, protection: area_protection_flags, source: area_id) -> area_id ---
	find_area           :: proc(name: cstring) -> area_id ---
	area_for            :: proc(address: rawptr) -> area_id ---
	delete_area         :: proc(id: area_id) -> status_t ---
	resize_area         :: proc(id: area_id, newSize: uint) -> status_t ---
	set_area_protection :: proc(id: area_id, newProtection: area_protection_flags) -> status_t ---
	_get_area_info      :: proc(id: area_id, areaInfo: ^area_info, size: uint) -> status_t ---
	_get_next_area_info :: proc(team: team_id, cookie: ^int, areaInfo: ^area_info, size: uint) -> status_t ---
}

// Ports

port_info :: struct {
	port:        port_id,
	team:        team_id,
	name:        [OS_NAME_LENGTH]byte,
	capacity:    i32, // queue depth
	queue_count: i32, // # msgs waiting to be read
	total_count: i32, // total # msgs read so far
}

port_flag :: enum u32 {
	USE_USER_MEMCPY   = intrinsics.constant_log2(0x80000000),
	// read the message, but don't remove it; kernel-only; memory must be locked
	PEEK_PORT_MESSAGE = intrinsics.constant_log2(0x100),
}
port_flags :: distinct bit_set[port_flag; u32]

@(default_calling_convention="c")
foreign libroot {
	create_port          :: proc(capacity: i32, name: cstring) -> port_id ---
	find_port            :: proc(name: cstring) -> port_id ---
	read_port            :: proc(port: port_id, code: ^i32, buffer: rawptr, bufferSize: uint) -> int ---
	read_port_etc        :: proc(port: port_id, code: ^i32, buffer: rawptr, bufferSize: uint, flags: port_flags, timeout: bigtime_t) -> int ---
	write_port           :: proc(port: port_id, code: i32, buffer: rawptr, bufferSize: uint) -> status_t ---
	write_port_etc       :: proc(port: port_id, code: i32, buffer: rawptr, bufferSize: uint, flags: port_flags, timeout: bigtime_t) -> status_t ---
	close_port           :: proc(port: port_id) -> status_t ---
	delete_port          :: proc(port: port_id) -> status_t ---
	port_buffer_size     :: proc(port: port_id) -> int ---
	port_buffer_size_etc :: proc(port: port_id, flags: port_flags, timeout: bigtime_t) -> int ---
	port_count           :: proc(port: port_id) -> int ---
	set_port_owner       :: proc(port: port_id, team: team_id) -> status_t ---
	_get_port_info       :: proc(port: port_id, portInfo: ^port_info, portInfoSize: uint) -> status_t ---
	_get_next_port_info  :: proc(team: team_id, cookie: ^i32, portInfo: ^port_info, portInfoSize: uint) -> status_t ---
}

// Semaphores

sem_info :: struct {
	sem:           sem_id,
	team:          team_id,
	name:          [OS_NAME_LENGTH]byte,
	count:         i32,
	latest_holder: thread_id,
}

semaphore_flag :: enum u32 {
	CAN_INTERRUPT      = intrinsics.constant_log2(0x01), // acquisition of the semaphore can be interrupted (system use only)
	CHECK_PERMISSION   = intrinsics.constant_log2(0x04), // ownership will be checked (system use only)
	KILL_CAN_INTERRUPT = intrinsics.constant_log2(0x20), // acquisition of the semaphore can be interrupted by SIGKILL[THR], even if not CAN_INTERRUPT (system use only)
	
	// release_sem_etc() only flags
	DO_NOT_RESCHEDULE       = intrinsics.constant_log2(0x02), // thread is not rescheduled
	RELEASE_ALL             = intrinsics.constant_log2(0x08), // all waiting threads will be woken up, count will be zeroed
	RELEASE_IF_WAITING_ONLY	= intrinsics.constant_log2(0x10), // release count only if there are any threads waiting
}
semaphore_flags :: distinct bit_set[semaphore_flag; u32]

@(default_calling_convention="c")
foreign libroot {
	create_sem         :: proc(count: i32, name: cstring) -> sem_id ---
	delete_sem         :: proc(id: sem_id) -> status_t ---
	acquire_sem        :: proc(id: sem_id) -> status_t ---
	acquire_sem_etc    :: proc(id: sem_id, count: i32, flags: semaphore_flags, timeout: bigtime_t) -> status_t ---
	release_sem        :: proc(id: sem_id) -> status_t ---
	release_sem_etc    :: proc(id: sem_id, count: i32, flags: semaphore_flags) -> status_t ---
	switch_sem         :: proc(semToBeReleased: sem_id) -> status_t ---
	switch_sem_etc     :: proc(semToBeReleased: sem_id, id: sem_id, count: i32, flags: semaphore_flags, timeout: bigtime_t) -> status_t ---
	get_sem_count      :: proc(id: sem_id, threadCount: ^i32) -> status_t ---
	set_sem_owner      :: proc(id: sem_id, team: team_id) -> status_t ---
	_get_sem_info      :: proc(id: sem_id, info: ^sem_info, infoSize: uint) -> status_t ---
	_get_next_sem_info :: proc(team: team_id, cookie: ^i32, info: ^sem_info, infoSize: uint) -> status_t ---
}

// Teams

team_info :: struct {
	team:                team_id,
	thread_count:        i32,
	image_count:         i32,
	area_count:          i32,
	debugger_nub_thread: thread_id,
	debugger_nub_port:   port_id,
	argc:                i32,
	args:                [64]byte,
	uid:                 uid_t,
	gid:                 gid_t,

	// Haiku R1 extensions
	real_uid:            uid_t,
	real_gid:            gid_t,
	group_id:            pid_t,
	session_id:          pid_t,
	parent:              team_id,
	name:                [OS_NAME_LENGTH]byte,
	start_time:          bigtime_t,
}

CURRENT_TEAM :: 0
SYSTEM_TEAM  :: 1

team_usage_info :: struct {
	user_time:   bigtime_t,
	kernel_time: bigtime_t,
}

team_usage_who :: enum i32 {
	// compatible to sys/resource.h RUSAGE_SELF and RUSAGE_CHILDREN
	SELF     = 0,
	CHILDREN = -1,
}

@(default_calling_convention="c")
foreign libroot {
	// see also: send_signal()
	kill_team            :: proc(team: team_id) -> status_t ---
	_get_team_info       :: proc(id: team_id, info: ^team_info, size: uint) -> status_t ---
	_get_next_team_info  :: proc(cookie: ^i32, info: ^team_info, size: uint) -> status_t ---
	_get_team_usage_info :: proc(id: team_id, who: team_usage_who, info: ^team_usage_info, size: uint) -> status_t ---
}

// Threads

thread_state :: enum i32 {
	RUNNING = 1,
	READY,
	RECEIVING,
	ASLEEP,
	SUSPENDED,
	WAITING,
}

thread_info :: struct {
	thread:      thread_id,
	team:        team_id,
	name:        [OS_NAME_LENGTH]byte,
	state:       thread_state,
	priority:    thread_priority,
	sem:         sem_id,
	user_time:   bigtime_t,
	kernel_time: bigtime_t,
	stack_base:  rawptr,
	stack_end:   rawptr,
}

thread_priority :: enum i32 {
	IDLE_PRIORITY              = 0,
	LOWEST_ACTIVE_PRIORITY     = 1,
	LOW_PRIORITY               = 5,
	NORMAL_PRIORITY            = 10,
	DISPLAY_PRIORITY           = 15,
	URGENT_DISPLAY_PRIORITY    = 20,
	REAL_TIME_DISPLAY_PRIORITY = 100,
	URGENT_PRIORITY            = 110,
	REAL_TIME_PRIORITY         = 120,
}

FIRST_REAL_TIME_PRIORITY :: thread_priority.REAL_TIME_PRIORITY

// time base for snooze_*(), compatible with the clockid_t constants defined in <time.h> 
SYSTEM_TIMEBASE :: 0

thread_func :: #type proc "c" (rawptr) -> status_t

@(default_calling_convention="c")
foreign libroot {
	spawn_thread          :: proc(thread_func, name: cstring, priority: thread_priority, data: rawptr) -> thread_id ---
	kill_thread           :: proc(thread: thread_id) -> status_t ---
	resume_thread         :: proc(thread: thread_id) -> status_t ---
	suspend_thread        :: proc(thread: thread_id) -> status_t ---
	rename_thread         :: proc(thread: thread_id, newName: cstring) -> status_t ---
	set_thread_priority   :: proc(thread: thread_id, newPriority: thread_priority) -> status_t ---
	exit_thread           :: proc(status: status_t) ---
	wait_for_thread       :: proc(thread: thread_id, returnValue: ^status_t) -> status_t ---
	// FIXME: Find and define those flags.
	wait_for_thread_etc   :: proc(id: thread_id, flags: u32, timeout: bigtime_t, _returnCode: ^status_t) -> status_t ---
	on_exit_thread        :: proc(callback: proc "c" (rawptr), data: rawptr) -> status_t ---
	find_thread           :: proc(name: cstring) -> thread_id ---
	send_data             :: proc(thread: thread_id, code: i32, buffer: rawptr, bufferSize: uint) -> status_t ---
	receive_data          :: proc(sender: ^thread_id, buffer: rawptr, bufferSize: uint) -> i32 ---
	has_data              :: proc(thread: thread_id) -> bool ---
	snooze                :: proc(amount: bigtime_t) -> status_t ---
	// FIXME: Find and define those flags.
	snooze_etc            :: proc(amount: bigtime_t, timeBase: i32, flags: u32) -> status_t ---
	snooze_until          :: proc(time: bigtime_t, timeBase: i32) -> status_t ---
	_get_thread_info      :: proc(id: thread_id, info: ^thread_info, size: uint) -> status_t ---
	_get_next_thread_info :: proc(team: team_id, cookie: ^i32, info: ^thread_info, size: uint) -> status_t ---
	// bridge to the pthread API
	get_pthread_thread_id :: proc(thread: pthread_t) -> thread_id ---
}

// Time

@(default_calling_convention="c")
foreign libroot {
	real_time_clock       :: proc() -> uint ---
	set_real_time_clock   :: proc(secsSinceJan1st1970: uint) ---
	real_time_clock_usecs :: proc() -> bigtime_t ---
	// time since booting in microseconds
	system_time           :: proc() -> bigtime_t ---
	// time since booting in nanoseconds
	system_time_nsecs     :: proc() -> nanotime_t ---
}

// Alarm

alarm_mode :: enum u32 {
	ONE_SHOT_ABSOLUTE_ALARM	= 1,
	ONE_SHOT_RELATIVE_ALARM,
	PERIODIC_ALARM, // "when" specifies the period
}

@(default_calling_convention="c")
foreign libroot {
	set_alarm :: proc(_when: bigtime_t, mode: alarm_mode) -> bigtime_t ---
}

// Debugger

@(default_calling_convention="c")
foreign libroot {
	debugger :: proc(message: cstring) ---
	/*
		calling this function with a non-zero value will cause your thread
		to receive signals for any exceptional conditions that occur (i.e.
		you'll get SIGSEGV for data access exceptions, SIGFPE for floating
		point errors, SIGILL for illegal instructions, etc).

		to re-enable the default debugger pass a zero.
	*/
	disable_debugger :: proc(state: i32) -> i32 ---
}

// System information

cpu_info :: struct {
	active_time:       bigtime_t,
	enabled:           bool,
	current_frequency: u64,
}

system_info :: struct {
	boot_time:         bigtime_t, // time of boot (usecs since 1/1/1970)

	cpu_count:         u32,       // number of cpus

	max_pages:         u64,       // total # of accessible pages
	used_pages:        u64,       // # of accessible pages in use
	cached_pages:      u64,
	block_cache_pages: u64,
	ignored_pages:     u64,	      // # of ignored/inaccessible pages

	needed_memory:     u64,
	free_memory:       u64,

	max_swap_pages:    u64,
	free_swap_pages:   u64,

	page_faults:       u32,	      // # of page faults

	max_sems:          u32,
	used_sems:         u32,

	max_ports:         u32,
	used_ports:        u32,

	max_threads:       u32,
	used_threads:      u32,

	max_teams:         u32,
	used_teams:        u32,

	kernel_name:       [FILE_NAME_LENGTH]byte,
	kernel_build_date: [OS_NAME_LENGTH]byte,
	kernel_build_time: [OS_NAME_LENGTH]byte,

	kernel_version:    i64,
	abi:               u32,       // the system API
}

topology_level_type :: enum i32 {
	UNKNOWN,
	ROOT,
	SMT,
	CORE,
	PACKAGE,
}

cpu_platform :: enum i32 {
	UNKNOWN,
	x86,
	x86_64,
	PPC,
	PPC_64,
	M68K,
	ARM,
	ARM_64,
	ALPHA,
	MIPS,
	SH,
	SPARC,
	RISC_V,
}

cpu_vendor :: enum i32 {
	UNKNOWN,
	AMD,
	CYRIX,
	IDT,
	INTEL,
	NATIONAL_SEMICONDUCTOR,
	RISE,
	TRANSMETA,
	VIA,
	IBM,
	MOTOROLA,
	NEC,
	HYGON,
	SUN,
	FUJITSU,
}

cpu_topology_node_info :: struct {
	id:            u32,
	type:          topology_level_type,
	level:         u32,

	data: struct #raw_union {
		_root: struct {
			platform: cpu_platform,
		},
		_package: struct {
			vendor:          cpu_vendor,
			cache_line_size: u32,
		},
		_core: struct {
			model:             u32,
			default_frequency: u64,
		},
	},
}

when ODIN_ARCH == .amd64 || ODIN_ARCH == .i386 {
	cpuid_info :: struct #raw_union {
		eax_0: struct {
			max_eax:   u32,
			vendor_id: [12]byte,
		},

		eax_1: struct {
			using _: bit_field u32 {
				stepping:        u32 | 4,
				model:           u32 | 4,
				family:          u32 | 4,
				type:            u32 | 2,
				reserved_0:      u32 | 2,
				extended_model:  u32 | 4,
				extended_family: u32 | 8,
				reserved_1:      u32 | 4,
			},

			using _: bit_field u32 {
				brand_index:  u32 | 8,
				clflush:      u32 | 8,
				logical_cpus: u32 | 8,
				apic_id:      u32 | 8,
			},

			features:          u32,
			extended_features: u32,
		},

		eax_2: struct {
			call_num:          u8,
			cache_descriptors: [15]u8,
		},

		eax_3: struct {
			reserved:           [2]u32,
			serial_number_high: u32,
			serial_number_low:  u32,
		},

		as_chars: [16]byte,

		regs: struct {
			eax: u32,
			ebx: u32,
			edx: u32,
			ecx: u32,
		},
	}
}

@(default_calling_convention="c")
foreign libroot {
	get_system_info       :: proc(info: ^system_info) -> status_t ---
	_get_cpu_info_etc     :: proc(firstCPU: u32, cpuCount: u32, info: ^cpu_info, size: uint) -> status_t ---
	get_cpu_topology_info :: proc(topologyInfos: [^]cpu_topology_node_info, topologyInfoCount: ^u32) -> status_t ---

	when ODIN_ARCH == .amd64 || ODIN_ARCH == .i386 {
		get_cpuid :: proc(info: ^cpuid_info, eaxRegister: u32, cpuNum: u32) -> status_t ---
	}

	is_computer_on      :: proc() -> i32 ---
	is_computer_on_fire :: proc() -> f64 ---
}

// POSIX signals

@(default_calling_convention="c")
foreign libroot {
	/*
	Wait for queued signals.

	[[ More; https://pubs.opengroup.org/onlinepubs/9699919799/functions/sigtimedwait.html ]]
	*/
	sigtimedwait :: proc(set: ^posix.sigset_t, info: ^posix.siginfo_t, timeout: ^posix.timespec) -> posix.result ---
}
