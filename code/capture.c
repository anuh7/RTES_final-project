/******************************************************************************
* @file: capture.c
* @brief: Final project code: standard synchronome. 
* @author: Anuhya
* @attributions: simple-capture-1800-syslog by Professor Sam Siewart
                 https://linuxtv.org/docs.php
* @date:  13-August-2023
*******************************************************************************/


// This is necessary for CPU affinity macros in Linux
#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <time.h>
#include <semaphore.h>
#include <fcntl.h>              /* low-level i/o */
#include <syslog.h>
#include <sys/time.h>
#include <sys/sysinfo.h>
#include <errno.h>
#include <sys/stat.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <string.h>
#include <linux/videodev2.h>

/*******************************************************************************
Defines
*******************************************************************************/
#define NSEC_PER_SEC (1000000000)
#define NSEC_PER_MSEC (1000000)
#define NSEC_PER_USEC (1000)
#define ERROR (-1)
#define OK (0)
#define NUM_CPU_CORES (4)
#define TRUE (1)
#define FALSE (0)
#define RT_CORE (2)
#define NUM_THREADS (3)
#define MY_CLOCK_TYPE CLOCK_MONOTONIC_RAW
#define CLEAR(x) memset(&(x), 0, sizeof(x))
#define MAX_HRES (1920)
#define MAX_VRES (1080)
#define MAX_PIXEL_SIZE (3)
#define HRES (640)
#define VRES (480)
#define PIXEL_SIZE (3)
#define HRES_STR "640"
#define VRES_STR "480"
#define STARTUP_FRAMES (30)
#define LAST_FRAMES (1)
#define FRAMES_PER_SEC (5) 
#define DRIVER_MMAP_BUFFERS (6)  
#define K 4.0
typedef double FLOAT;

typedef unsigned int UINT32;
typedef unsigned long long int UINT64;
typedef unsigned char UINT8;

FLOAT PSF[9] = {-K/8.0, -K/8.0, -K/8.0, -K/8.0, K+1.0, -K/8.0, -K/8.0, -K/8.0, -K/8.0};


/*******************************************************************************
Global Variables
*******************************************************************************/
static struct v4l2_format fmt;
struct v4l2_buffer frame_buf;

struct buffer 
{
        void   *start;
        size_t  length;
};


struct save_frame_t
{
    unsigned char   frame[HRES*VRES*PIXEL_SIZE];
};

struct ring_buffer_t
{
    unsigned int ring_size;

    int tail_idx;
    int head_idx;
    int count;

    struct save_frame_t save_frame[1*FRAMES_PER_SEC];
};

static struct cb_fifo_t     cb_fifo;
static  struct ring_buffer_t	ring_buffer;

struct cb_fifo_t
{
    unsigned int cb_fifo_size;
    int tail;
    int head;
    int count;

    struct save_frame_t transform_frame[60];
};

static int              camera_device_fd = -1;
struct buffer          *buffers;
static unsigned int     n_buffers;
static int              force_format=1;


static struct timespec time_now;
static double fnow;
static int frame_count;

int abortTest=FALSE;
int abortS1=FALSE, abortS2=FALSE, abortS3=FALSE, abortS4=FALSE;
sem_t semS1, semS2;    
struct timespec start_time_val, current_time_res;
double start_realtime, current_realtime_res;
int s1_cnt=0 , s2_cnt=0, ppm_flag=0, negative_transform_flag = 0; 

int head_inc = 0;
int head_inc_after = 0;
int buffer_count = 0;


static timer_t timer_1;
static struct itimerspec itime = {{1,0}, {1,0}};
static struct itimerspec last_itime;

static unsigned long long seqCnt=0;

typedef struct
{
    int threadIdx;
} threadParams_t;


/*******************************************************************************
Function Prototypes
*******************************************************************************/
void Sequencer(int id);
void *Service_1_frame_acquisition(void *threadp);
void *Service_2_frame_process(void *threadp);
void *Service_3_frame_storage(void *threadp);
int seq_frame_read(void);
int seq_frame_process(void);
void seq_frame_sharpen(void);
void seq_frame_transform(void);
int seq_frame_store(void);
double getTimeMsec(void);
double realtime(struct timespec *tsptr);
void print_scheduler(void);
int v4l2_frame_acquisition_initialization(char *dev_name);
int v4l2_frame_acquisition_shutdown(void);
int v4l2_frame_acquisition_loop(char *dev_name);
void sharpen_image(const void *ptr, int size);
void convert_to_negative(unsigned char *r, unsigned char *g, unsigned char *b);
void negative_image(const void *ptr, int size);


int main(void)
{

    char *dev_name="/dev/video0";

    int i, rc, scope, flags=0;

    cpu_set_t threadcpu;
    cpu_set_t allcpuset;

    int input;

    pthread_t threads[NUM_THREADS];
    threadParams_t threadParams[NUM_THREADS];
    pthread_attr_t rt_sched_attr[NUM_THREADS];
    int rt_max_prio, rt_min_prio, cpuidx;

    struct sched_param rt_param[NUM_THREADS];
    struct sched_param main_param;

    pthread_attr_t main_attr;
    pid_t mainpid;

    cb_fifo.tail = 0;
    cb_fifo.head = 0;
    cb_fifo.count = 0;
    cb_fifo.cb_fifo_size = 180;

    v4l2_frame_acquisition_initialization(dev_name);

   printf("System has %d processors configured and %d available.\n", get_nprocs_conf(), get_nprocs());

   CPU_ZERO(&allcpuset);

   for(i=0; i < NUM_CPU_CORES; i++)
       CPU_SET(i, &allcpuset);

   printf("Using CPUS=%d from total available.\n", CPU_COUNT(&allcpuset));

    if (sem_init (&semS1, 0, 0)) { printf ("Failed to initialize S1 semaphore\n"); exit (-1); }
    if (sem_init (&semS2, 0, 0)) { printf ("Failed to initialize S2 semaphore\n"); exit (-1); }

    mainpid=getpid();

    rt_max_prio = sched_get_priority_max(SCHED_FIFO);
    rt_min_prio = sched_get_priority_min(SCHED_FIFO);

    rc=sched_getparam(mainpid, &main_param);
    main_param.sched_priority=rt_max_prio;
    rc=sched_setscheduler(getpid(), SCHED_FIFO, &main_param);
    if(rc < 0) perror("main_param");
    print_scheduler();


    pthread_attr_getscope(&main_attr, &scope);

    if(scope == PTHREAD_SCOPE_SYSTEM)
      printf("PTHREAD SCOPE SYSTEM\n");
    else if (scope == PTHREAD_SCOPE_PROCESS)
      printf("PTHREAD SCOPE PROCESS\n");
    else
      printf("PTHREAD SCOPE UNKNOWN\n");

    printf("rt_max_prio=%d\n", rt_max_prio);
    printf("rt_min_prio=%d\n", rt_min_prio);


    for(i=0; i < NUM_THREADS; i++)
    {

      CPU_ZERO(&threadcpu);
      cpuidx=(RT_CORE);
      CPU_SET(cpuidx, &threadcpu);

      rc=pthread_attr_init(&rt_sched_attr[i]);
      rc=pthread_attr_setinheritsched(&rt_sched_attr[i], PTHREAD_EXPLICIT_SCHED);
      rc=pthread_attr_setschedpolicy(&rt_sched_attr[i], SCHED_FIFO);
      rc=pthread_attr_setaffinity_np(&rt_sched_attr[i], sizeof(cpu_set_t), &threadcpu);

      rt_param[i].sched_priority=rt_max_prio-i;
      pthread_attr_setschedparam(&rt_sched_attr[i], &rt_param[i]);

      threadParams[i].threadIdx=i;
    }

    
    printf("\n*********************Input a command*********************\n");
    printf("Press 1 to acquire @ 1 Hz for 3 minutes \n");
    printf("Press 2 to acquire @ 1 Hz with negative transformation for 3 minutes \n");
    printf("Press 3 to acquire @ 10 Hz for 3 minutes \n");
    printf("Press 4 to acquire @ 10 Hz with negative transformatio for 3 minutes \n");

    printf("\n Pressed option:");
    here: scanf("%d", &input);

    switch(input)
    {
        case 1:
            s1_cnt = 20;
            s2_cnt = 100;
            ppm_flag = 1;
            negative_transform_flag = 0;
            head_inc = 2;
            head_inc_after = 3;
            buffer_count = 5;
            frame_count = 180;
            break;
        
        case 2:
            s1_cnt = 20;
            s2_cnt = 100;
            ppm_flag = 1;
            negative_transform_flag = 1;
            head_inc = 2;
            head_inc_after = 3;
            buffer_count = 5;
            frame_count = 180;
            break;

        case 3:
            s1_cnt = 5;
            s2_cnt = 10;
            ppm_flag = 0;
            negative_transform_flag = 0;
            head_inc = 1;
            head_inc_after = 1;
            buffer_count = 2;
            frame_count = 1800;
            break;

        case 4:
            s1_cnt = 5;
            s2_cnt = 10;
            ppm_flag = 0;
            negative_transform_flag = 1;
            head_inc = 1;
            head_inc_after = 1;
            buffer_count = 2;
            frame_count = 1800;
            break;

        default:
            printf("Enter a valid input \n");
            goto here;

    }

    ring_buffer.tail_idx=0;
	ring_buffer.head_idx=0;
	ring_buffer.count=0;
	ring_buffer.ring_size=buffer_count;

   
    printf("Starting High Rate Sequencer Demo\n");
    clock_gettime(MY_CLOCK_TYPE, &start_time_val); start_realtime=realtime(&start_time_val);
    clock_getres(MY_CLOCK_TYPE, &current_time_res); current_realtime_res=realtime(&current_time_res);
    printf("START High Rate Sequencer @ sec=%6.9lf with resolution %6.9lf\n", start_realtime, current_realtime_res);
    syslog(LOG_CRIT, "START High Rate Sequencer @ sec=%6.9lf with resolution %6.9lf\n", start_realtime, current_realtime_res);

    printf("Service threads will run on %d CPU cores\n", CPU_COUNT(&threadcpu));

    // Servcie_1 = RT_MAX-1	@ 25 Hz
    //
    rt_param[0].sched_priority=rt_max_prio-1;
    pthread_attr_setschedparam(&rt_sched_attr[0], &rt_param[0]);
    rc=pthread_create(&threads[0],               // pointer to thread descriptor
                      &rt_sched_attr[0],         // use specific attributes
                      //(void *)0,               // default attributes
                      Service_1_frame_acquisition,                 // thread function entry point
                      (void *)&(threadParams[0]) // parameters to pass in
                     );
    if(rc < 0)
        perror("pthread_create for service 1 - V4L2 video frame acquisition");
    else
        printf("pthread_create successful for service 1\n");


    // Service_2 = RT_MAX-2	@ 1 Hz
    //
    rt_param[1].sched_priority=rt_max_prio-2;
    pthread_attr_setschedparam(&rt_sched_attr[1], &rt_param[1]);
    rc=pthread_create(&threads[1], &rt_sched_attr[1], Service_2_frame_process, (void *)&(threadParams[1]));
    if(rc < 0)
        perror("pthread_create for service 2 - flash frame storage");
    else
        printf("pthread_create successful for service 2\n");
    
    CPU_ZERO(&threadcpu);
	CPU_SET(3, &threadcpu);
    rc=pthread_attr_setaffinity_np(&rt_sched_attr[2], sizeof(cpu_set_t), &threadcpu);
    rt_param[2].sched_priority=rt_max_prio-6;
    pthread_attr_setschedparam(&rt_sched_attr[2], &rt_param[2]);
    rc=pthread_create(&threads[2], &rt_sched_attr[2], Service_3_frame_storage, (void *)&(threadParams[2]));
    if(rc < 0)
        perror("pthread_create for service 3 - flash frame storage");
    else
        printf("pthread_create successful for service 3\n");


 
    printf("Start sequencer\n");

    // Sequencer = RT_MAX	@ 100 Hz
    //
    /* set up to signal SIGALRM if timer expires */
    timer_create(CLOCK_REALTIME, NULL, &timer_1);


    signal(SIGALRM, (void(*)()) Sequencer);


    /* arm the interval timer */
    itime.it_interval.tv_sec = 0;
    itime.it_interval.tv_nsec = 10000000;
    itime.it_value.tv_sec = 0;
    itime.it_value.tv_nsec = 10000000;


    timer_settime(timer_1, flags, &itime, &last_itime);


    for(i=0;i<NUM_THREADS;i++)
    {
        if((rc=pthread_join(threads[i], NULL)) < 0)
		perror("main pthread_join");
	else
		printf("joined thread %d\n", i);
    }

   v4l2_frame_acquisition_shutdown();

   printf("\nTEST COMPLETE\n");

   return 0;
}



void Sequencer(int id)
{
    int flags=0;
    if(abortTest)
    {
        // disable interval timer
        itime.it_interval.tv_sec = 0;
        itime.it_interval.tv_nsec = 0;
        itime.it_value.tv_sec = 0;
        itime.it_value.tv_nsec = 0;
        timer_settime(timer_1, flags, &itime, &last_itime);
	    printf("Disabling sequencer interval timer with abort=%d and %llu\n", abortTest, seqCnt);

	    // shutdown all services
        abortS1=TRUE; abortS2=TRUE; abortS3=TRUE; abortS4=TRUE;
        sem_post(&semS1); sem_post(&semS2); //sem_post(&semS3);  

    }

    seqCnt++;

    // Servcie_1 @ 5 Hz
    if((seqCnt % s1_cnt) == 0) sem_post(&semS1);

    // Service_2 @ 1 Hz
    if((seqCnt % s2_cnt) == 0) sem_post(&semS2);

}




void *Service_1_frame_acquisition(void *threadp)
{
    struct timespec current_time_val;
    double current_realtime, time1, time2;
    unsigned long long S1Cnt=0;
    
    clock_gettime(MY_CLOCK_TYPE, &current_time_val); current_realtime=realtime(&current_time_val);
    syslog(LOG_CRIT, "S1 thread @ sec=%6.9lf\n", current_realtime-start_realtime);

    while(!abortS1) 
    {
        sem_wait(&semS1);
	    if(abortS1) break;

        time1 = getTimeMsec();
    
        S1Cnt++;
	    seq_frame_read();

        time2 = getTimeMsec();

        clock_gettime(MY_CLOCK_TYPE, &current_time_val); current_realtime=realtime(&current_time_val);
        syslog(LOG_CRIT, "S1 5 Hz on core %d for release %llu @ sec=%6.9lf, exec time=%6.9lf\n", sched_getcpu(), S1Cnt, current_realtime-start_realtime, time2 - time1);

    }
    pthread_exit((void *)0);
}


void *Service_2_frame_process(void *threadp)
{
    unsigned long long S2Cnt=0;
    struct timespec current_time_val;
    double current_realtime, time1, time2;

    clock_gettime(MY_CLOCK_TYPE, &current_time_val); current_realtime=realtime(&current_time_val);
    syslog(LOG_CRIT, "S2 thread @ sec=%6.9lf\n", current_realtime-start_realtime);

    while(!abortS2)
    {
        sem_wait(&semS2);

	    if(abortS2) break;
        S2Cnt++;

        time1 = getTimeMsec();
        seq_frame_process();
        time2 = getTimeMsec();

        clock_gettime(MY_CLOCK_TYPE, &current_time_val); current_realtime=realtime(&current_time_val);
        syslog(LOG_CRIT, "S2 1 Hz on core %d for release %llu @ sec=%6.9lf, exec time=%6.9lf\n", sched_getcpu(), S2Cnt, current_realtime-start_realtime, time2- time1);
     
	    if(S2Cnt == (frame_count + STARTUP_FRAMES + LAST_FRAMES)) {abortTest=TRUE;};
    }

    pthread_exit((void *)0);
}


void *Service_3_frame_storage(void *threadp)
{
    struct timespec current_time_val;
    double current_realtime;

    clock_gettime(MY_CLOCK_TYPE, &current_time_val); current_realtime=realtime(&current_time_val);
    syslog(LOG_CRIT, "S3 thread @ sec=%6.9lf\n", current_realtime-start_realtime);

    while(!abortS3)
    {
	    if(abortS3) break;
        seq_frame_store();
     }

    pthread_exit((void *)0);
}


static void errno_exit(const char *s)
{
        fprintf(stderr, "%s error %d, %s\n", s, errno, strerror(errno));
        exit(EXIT_FAILURE);
}


static int xioctl(int fh, int request, void *arg)
{
    int rc;

    do 
    {
        rc = ioctl(fh, request, arg);

    } while (-1 == rc && EINTR == errno);

    return rc;
}

char ppm_header[]="P6\n#9999999999 sec 9999999999 msec \n"HRES_STR" "VRES_STR"\n255\n";
char ppm_dumpname[]="frames/test0000.ppm";

static void dump_ppm(const void *p, int size, unsigned int tag, struct timespec *time)
{
    int written, total, dumpfd;
   
    snprintf(&ppm_dumpname[11], 9, "%04d", tag);
    strncat(&ppm_dumpname[15], ".ppm", 5);
    dumpfd = open(ppm_dumpname, O_WRONLY | O_NONBLOCK | O_CREAT, 00666);

    snprintf(&ppm_header[4], 11, "%010d", (int)time->tv_sec);
    strncat(&ppm_header[14], " sec ", 5);
    snprintf(&ppm_header[19], 11, "%010d", (int)((time->tv_nsec)/1000000));
    strncat(&ppm_header[29], " msec \n"HRES_STR" "VRES_STR"\n255\n", 19);

    // subtract 1 from sizeof header because it includes the null terminator for the string
    written=write(dumpfd, ppm_header, sizeof(ppm_header)-1);

    total=0;

    do
    {
        written=write(dumpfd, p, size);
        total+=written;
    } while(total < size);
    close(dumpfd);
    
}


char pgm_header[]="P5\n#9999999999 sec 9999999999 msec \n"HRES_STR" "VRES_STR"\n255\n";
char pgm_dumpname[]="frames/test0000.pgm";

static void dump_pgm(const void *p, int size, unsigned int tag, struct timespec *time)
{
    int written, total, dumpfd;
   
    snprintf(&pgm_dumpname[11], 9, "%04d", tag);
    strncat(&pgm_dumpname[15], ".pgm", 5);
    dumpfd = open(pgm_dumpname, O_WRONLY | O_NONBLOCK | O_CREAT, 00666);

    snprintf(&pgm_header[4], 11, "%010d", (int)time->tv_sec);
    strncat(&pgm_header[14], " sec ", 5);
    snprintf(&pgm_header[19], 11, "%010d", (int)((time->tv_nsec)/1000000));
    strncat(&pgm_header[29], " msec \n"HRES_STR" "VRES_STR"\n255\n", 19);

    // subtract 1 from sizeof header because it includes the null terminator for the string
    written=write(dumpfd, pgm_header, sizeof(pgm_header)-1);

    total=0;

    do
    {
        written=write(dumpfd, p, size);
        total+=written;
    } while(total < size);

    close(dumpfd);
    
}


void yuv2rgb(int y, int u, int v, unsigned char *r, unsigned char *g, unsigned char *b)
{
   int r1, g1, b1;

   // replaces floating point coefficients
   int c = y-16, d = u - 128, e = v - 128;       

   // Conversion that avoids floating point
   r1 = (298 * c           + 409 * e + 128) >> 8;
   g1 = (298 * c - 100 * d - 208 * e + 128) >> 8;
   b1 = (298 * c + 516 * d           + 128) >> 8;

   // Computed values may need clipping.
   if (r1 > 255) r1 = 255;
   if (g1 > 255) g1 = 255;
   if (b1 > 255) b1 = 255;

   if (r1 < 0) r1 = 0;
   if (g1 < 0) g1 = 0;
   if (b1 < 0) b1 = 0;

   *r = r1 ;
   *g = g1 ;
   *b = b1 ;
}


// always ignore STARTUP_FRAMES while camera adjusts to lighting, focuses, etc.
int read_framecnt=-STARTUP_FRAMES;
int process_framecnt=0;
int save_framecnt=-STARTUP_FRAMES;

unsigned char scratchpad_buffer[MAX_HRES*MAX_VRES*MAX_PIXEL_SIZE];

void convert_to_negative(unsigned char *r, unsigned char *g, unsigned char *b)
{
    *r = 255 - *r;
    *g = 255 - *g;
    *b = 255 - *b;
}

void negative_image(const void *ptr, int size)
{
    unsigned char *frame_ptr = (unsigned char *)ptr;

    for(int i=0, newi=0; i<size; i=i+4, newi=newi+6)
    {
        convert_to_negative(&frame_ptr[newi], &frame_ptr[newi+1], &frame_ptr[newi+2]);
        convert_to_negative(&frame_ptr[newi+3], &frame_ptr[newi+4], &frame_ptr[newi+5]);
    }
}


static int save_image(const void *p, int size, struct timespec *frame_time)
{
    unsigned char *frame_ptr = (unsigned char *)p;
    save_framecnt++;

if(ppm_flag)
{
    if(save_framecnt > 0) 
        {
             dump_ppm(frame_ptr, ((size*6)/4), save_framecnt, frame_time);
        }
}
else
{
    if(save_framecnt > 0)
        {
            dump_pgm(frame_ptr, (size/2), save_framecnt, frame_time);
        }
}

    return save_framecnt;
}

static int process_image(const void *p, int size)
{
    int i, newi;
    int y_temp, y2_temp, u_temp, v_temp;
    unsigned char *frame_ptr = (unsigned char *)p;

    process_framecnt++;


if(ppm_flag)
{
    for(i=0, newi=0; i<size; i=i+4, newi=newi+6)
        {
            y_temp=(int)frame_ptr[i]; u_temp=(int)frame_ptr[i+1]; y2_temp=(int)frame_ptr[i+2]; v_temp=(int)frame_ptr[i+3];
            yuv2rgb(y_temp, u_temp, v_temp, &scratchpad_buffer[newi], &scratchpad_buffer[newi+1], &scratchpad_buffer[newi+2]);
            yuv2rgb(y2_temp, u_temp, v_temp, &scratchpad_buffer[newi+3], &scratchpad_buffer[newi+4], &scratchpad_buffer[newi+5]);
        }
}
else
{
    for(i=0, newi=0; i<size; i=i+4, newi=newi+2)
        {
            scratchpad_buffer[newi]=frame_ptr[i];
            scratchpad_buffer[newi+1]=frame_ptr[i+2];
        }
}

if(negative_transform_flag == 1)
{
    negative_image(scratchpad_buffer, (HRES*VRES*PIXEL_SIZE));
}

    memcpy((void *)&(cb_fifo.transform_frame[cb_fifo.tail].frame[0]), scratchpad_buffer, HRES*VRES*PIXEL_SIZE);
    
    cb_fifo.tail = (cb_fifo.tail + 1) % cb_fifo.cb_fifo_size;
    cb_fifo.count++;
    
    return process_framecnt;
}



static int read_frame(void)
{
    CLEAR(frame_buf);

    frame_buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
    frame_buf.memory = V4L2_MEMORY_MMAP;

    if (-1 == xioctl(camera_device_fd, VIDIOC_DQBUF, &frame_buf))
    {
        switch (errno)
        {
            case EAGAIN:
                return 0;

            case EIO:
                return 0;


            default:
                printf("mmap failure\n");
                errno_exit("VIDIOC_DQBUF");
        }
    }

    read_framecnt++;

    if(read_framecnt == 0) 
    {
            //fstart
    }

    assert(frame_buf.index < n_buffers);

    return 1;
}


int seq_frame_read(void)
{
    fd_set fds;
    struct timeval tv;
    

    FD_ZERO(&fds);
    FD_SET(camera_device_fd, &fds);

    /* Timeout */
    tv.tv_sec = 2;
    tv.tv_usec = 0;

    select(camera_device_fd + 1, &fds, NULL, NULL, &tv);

    read_frame();

    memcpy((void *)&(ring_buffer.save_frame[ring_buffer.tail_idx].frame[0]), buffers[frame_buf.index].start, frame_buf.bytesused);

    ring_buffer.tail_idx = (ring_buffer.tail_idx + 1) % ring_buffer.ring_size;
    ring_buffer.count++;

    if (-1 == xioctl(camera_device_fd, VIDIOC_QBUF, &frame_buf))
        errno_exit("VIDIOC_QBUF");

    return 0;
}

int seq_frame_process(void)
{
    int cnt;

    ring_buffer.head_idx = (ring_buffer.head_idx + head_inc) % ring_buffer.ring_size;

    cnt=process_image((void *)&(ring_buffer.save_frame[ring_buffer.head_idx].frame[0]), HRES*VRES*PIXEL_SIZE);

    ring_buffer.head_idx = (ring_buffer.head_idx + head_inc_after) % ring_buffer.ring_size;
    ring_buffer.count = ring_buffer.count - buffer_count;

    if(process_framecnt > 0)
    {	
        clock_gettime(CLOCK_MONOTONIC, &time_now);
        fnow = realtime(&time_now);
    }
    return cnt;
}

int seq_frame_store(void)
{
    int cnt;

   if(cb_fifo.count)
    {         
        cnt=save_image((void *)&(cb_fifo.transform_frame[cb_fifo.head].frame[0]), HRES*VRES*PIXEL_SIZE, &time_now);
        cb_fifo.head = (cb_fifo.head + 1) % cb_fifo.cb_fifo_size;
        cb_fifo.count = cb_fifo.count - 1;
        
    }

    return cnt;
}

static void stop_capturing(void)
{
    enum v4l2_buf_type type;

    type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if(-1 == xioctl(camera_device_fd, VIDIOC_STREAMOFF, &type))
		    errno_exit("VIDIOC_STREAMOFF");

    printf("capture stopped\n");
}


static void start_capturing(void)
{
        unsigned int i;
        enum v4l2_buf_type type;

	printf("will capture to %d buffers\n", n_buffers);

        for (i = 0; i < n_buffers; ++i) 
        {
                printf("allocated buffer %d\n", i);

                CLEAR(frame_buf);
                frame_buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                frame_buf.memory = V4L2_MEMORY_MMAP;
                frame_buf.index = i;

                if (-1 == xioctl(camera_device_fd, VIDIOC_QBUF, &frame_buf))
                        errno_exit("VIDIOC_QBUF");
        }

        type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

        if (-1 == xioctl(camera_device_fd, VIDIOC_STREAMON, &type))
                errno_exit("VIDIOC_STREAMON");

}


static void uninit_device(void)
{
        unsigned int i;

        for (i = 0; i < n_buffers; ++i)
                if (-1 == munmap(buffers[i].start, buffers[i].length))
                        errno_exit("munmap");

        free(buffers);
}


static void init_mmap(char *dev_name)
{
        struct v4l2_requestbuffers req;

        CLEAR(req);

        req.count = DRIVER_MMAP_BUFFERS;
        req.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        req.memory = V4L2_MEMORY_MMAP;

	printf("init_mmap req.count=%d\n",req.count);

        if (-1 == xioctl(camera_device_fd, VIDIOC_REQBUFS, &req)) 
        {
                if (EINVAL == errno) 
                {
                        fprintf(stderr, "%s does not support "
                                 "memory mapping\n", dev_name);
                        exit(EXIT_FAILURE);
                } else 
                {
                        errno_exit("VIDIOC_REQBUFS");
                }
        }

        if (req.count < 2) 
        {
                fprintf(stderr, "Insufficient buffer memory on %s\n", dev_name);
                exit(EXIT_FAILURE);
        }
	else
	{
	    printf("Device supports %d mmap buffers\n", req.count);

	    // allocate tracking buffers array for those that are mapped
            buffers = calloc(req.count, sizeof(*buffers));

	}

        if (!buffers) 
        {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }

        for (n_buffers = 0; n_buffers < req.count; ++n_buffers) 
	{
                CLEAR(frame_buf);

                frame_buf.type        = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                frame_buf.memory      = V4L2_MEMORY_MMAP;
                frame_buf.index       = n_buffers;

                if (-1 == xioctl(camera_device_fd, VIDIOC_QUERYBUF, &frame_buf))
                        errno_exit("VIDIOC_QUERYBUF");

                buffers[n_buffers].length = frame_buf.length;
                buffers[n_buffers].start =
                        mmap(NULL /* start anywhere */,
                              frame_buf.length,
                              PROT_READ | PROT_WRITE /* required */,
                              MAP_SHARED /* recommended */,
                              camera_device_fd, frame_buf.m.offset);

                if (MAP_FAILED == buffers[n_buffers].start)
                        errno_exit("mmap");

                printf("mappped buffer %d\n", n_buffers);
        }
}


static void init_device(char *dev_name)
{
    struct v4l2_capability cap;
    struct v4l2_cropcap cropcap;
    struct v4l2_crop crop;
    unsigned int min;

    if (-1 == xioctl(camera_device_fd, VIDIOC_QUERYCAP, &cap))
    {
        if (EINVAL == errno) {
            fprintf(stderr, "%s is no V4L2 device\n",
                     dev_name);
            exit(EXIT_FAILURE);
        }
        else
        {
                errno_exit("VIDIOC_QUERYCAP");
        }
    }

    if (!(cap.capabilities & V4L2_CAP_VIDEO_CAPTURE))
    {
        fprintf(stderr, "%s is no video capture device\n",
                 dev_name);
        exit(EXIT_FAILURE);
    }

    if (!(cap.capabilities & V4L2_CAP_STREAMING))
    {
        fprintf(stderr, "%s does not support streaming i/o\n",
                 dev_name);
        exit(EXIT_FAILURE);
    }

    CLEAR(cropcap);

    cropcap.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if (0 == xioctl(camera_device_fd, VIDIOC_CROPCAP, &cropcap))
    {
        crop.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        crop.c = cropcap.defrect; /* reset to default */

        if (-1 == xioctl(camera_device_fd, VIDIOC_S_CROP, &crop))
        {
            switch (errno)
            {
                case EINVAL:
                    break;
                default:
                        break;
            }
        }

    }
    else

    CLEAR(fmt);

    fmt.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if (force_format)
    {
        printf("FORCING FORMAT\n");
        fmt.fmt.pix.width       = HRES;
        fmt.fmt.pix.height      = VRES;

        fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_YUYV;
        fmt.fmt.pix.field       = V4L2_FIELD_NONE;

        if (-1 == xioctl(camera_device_fd, VIDIOC_S_FMT, &fmt))
                errno_exit("VIDIOC_S_FMT");

    }
    else
    {
        printf("ASSUMING FORMAT\n");
        if (-1 == xioctl(camera_device_fd, VIDIOC_G_FMT, &fmt))
                    errno_exit("VIDIOC_G_FMT");
    }

    /* Buggy driver paranoia. */
    min = fmt.fmt.pix.width * 2;
    if (fmt.fmt.pix.bytesperline < min)
            fmt.fmt.pix.bytesperline = min;
    min = fmt.fmt.pix.bytesperline * fmt.fmt.pix.height;
    if (fmt.fmt.pix.sizeimage < min)
            fmt.fmt.pix.sizeimage = min;

    init_mmap(dev_name);
}


static void close_device(void)
{
        if (-1 == close(camera_device_fd))
                errno_exit("close");

        camera_device_fd = -1;
}


static void open_device(char *dev_name)
{
        struct stat st;

        if (-1 == stat(dev_name, &st)) {
                fprintf(stderr, "Cannot identify '%s': %d, %s\n",
                         dev_name, errno, strerror(errno));
                exit(EXIT_FAILURE);
        }

        if (!S_ISCHR(st.st_mode)) {
                fprintf(stderr, "%s is no device\n", dev_name);
                exit(EXIT_FAILURE);
        }

        camera_device_fd = open(dev_name, O_RDWR /* required */ | O_NONBLOCK, 0);

        if (-1 == camera_device_fd) {
                fprintf(stderr, "Cannot open '%s': %d, %s\n",
                         dev_name, errno, strerror(errno));
                exit(EXIT_FAILURE);
        }
}


int v4l2_frame_acquisition_initialization(char *dev_name)
{
    // initialization of V4L2
    open_device(dev_name);
    init_device(dev_name);

    start_capturing();
    return 0;
}


int v4l2_frame_acquisition_shutdown(void)
{
    stop_capturing();
    uninit_device();
    close_device();
    fprintf(stderr, "\n");
    return 0;
}



double getTimeMsec(void)
{
  struct timespec event_ts = {0, 0};

  clock_gettime(MY_CLOCK_TYPE, &event_ts);
  return ((event_ts.tv_sec)*1000.0) + ((event_ts.tv_nsec)/1000000.0);
}


double realtime(struct timespec *tsptr)
{
    return ((double)(tsptr->tv_sec) + (((double)tsptr->tv_nsec)/1000000000.0));
}


void print_scheduler(void)
{
   int schedType;

   schedType = sched_getscheduler(getpid());

   switch(schedType)
   {
       case SCHED_FIFO:
           printf("Pthread Policy is SCHED_FIFO\n");
           break;
       case SCHED_OTHER:
           printf("Pthread Policy is SCHED_OTHER\n"); exit(-1);
         break;
       case SCHED_RR:
           printf("Pthread Policy is SCHED_RR\n"); exit(-1);
           break;
       default:
           printf("Pthread Policy is UNKNOWN\n"); exit(-1);
   }
}
