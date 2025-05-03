#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "gbn.h"

/* ******************************************************************
   Go Back N protocol.  Adapted from J.F.Kurose
   ALTERNATING BIT AND GO-BACK-N NETWORK EMULATOR: VERSION 1.2

   Network properties:
   - one way network delay averages five time units (longer if there
   are other messages in the channel for GBN), but can be larger
   - packets can be corrupted (either the header or the data portion)
   or lost, according to user-defined probabilities
   - packets will be delivered in the order in which they were sent
   (although some can be lost).

   Modifications:
   - removed bidirectional GBN code and other code not used by prac.
   - fixed C style to adhere to current programming style
   - added GBN implementation
**********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet
                          MUST BE SET TO 6 when submitting assignment */
#define SEQSPACE 7      /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ )
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}


/********* Sender (A) variables and functions ************/

static struct pkt buffer[WINDOWSIZE];  /* array for storing packets waiting for ACK */
static bool acked[WINDOWSIZE];          /* mark whether each packet in window is acked */
static bool timer_running[WINDOWSIZE];  /* track timer status */
static int base;                        /* base of the window */
static int nextseqnum;                  /* sequence number for next packet to send */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
    int i;
    if ((nextseqnum + SEQSPACE - base) % SEQSPACE < WINDOWSIZE) {
        struct pkt sendpkt;
        sendpkt.seqnum = nextseqnum;
        sendpkt.acknum = NOTINUSE;
        for (i = 0; i < 20; i++)
            sendpkt.payload[i] = message.data[i];
        sendpkt.checksum = ComputeChecksum(sendpkt);

        /* send packet to layer 3 */
        tolayer3(A, sendpkt);
        if (TRACE > 0)
            printf("A: Sent packet %d\n", sendpkt.seqnum);

        /* save to buffer */
        buffer[nextseqnum % WINDOWSIZE] = sendpkt;
        acked[nextseqnum % WINDOWSIZE] = false;

        /* start timer */
        if (!timer_running[nextseqnum % WINDOWSIZE]) {
            starttimer(A, RTT);
            timer_running[nextseqnum % WINDOWSIZE] = true;
        }

        nextseqnum = (nextseqnum + 1) % SEQSPACE;
    } else {
        if (TRACE > 0)
            printf("A: Window full, message dropped or buffered\n");
    }
}


/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{
    int acknum;
    int index;

    if (IsCorrupted(packet)) {
        if (TRACE > 0)
            printf("A: Received corrupted ACK, ignored.\n");
        return;
    }

    acknum = packet.acknum;
    total_ACKs_received++;
    new_ACKs++;
    if (TRACE > 0)
        printf("A: Received ACK for %d\n", acknum);

    index = acknum % WINDOWSIZE;

    /* mark this packet as acked */
    acked[index] = true;

    /* if it is base, try to move window forward */
    while (acked[base % WINDOWSIZE]) {
        if (TRACE > 0)
            printf("A: Sliding window, base %d acknowledged\n", base);
        acked[base % WINDOWSIZE] = false;
        timer_running[base % WINDOWSIZE] = false;
        base = (base + 1) % SEQSPACE;

        /* restart timer for new base */
        stoptimer(A);
        if (base != nextseqnum) {
            starttimer(A, RTT);
            timer_running[base % WINDOWSIZE] = true;
        }
    }
}


/* called when A's timer goes off */
void A_timerinterrupt(void)
{
    if (!acked[base % WINDOWSIZE]) {
        if (TRACE > 0)
            printf("A: Timer expired for packet %d, retransmitting.\n", base);

        tolayer3(A, buffer[base % WINDOWSIZE]);
        packets_resent++;

        /* restart timer */
        starttimer(A, RTT);
        timer_running[base % WINDOWSIZE] = true;
    }
}



/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
    int i;
    base = 0;
    nextseqnum = 0;
    for (i = 0; i < WINDOWSIZE; i++) {
        acked[i] = false;
        timer_running[i] = false;
    }
}


/********* Receiver (B)  variables and procedures ************/

static struct pkt recv_buffer[SEQSPACE]; /* buffer to store received packets */
static bool received[SEQSPACE];          /* mark if a packet has been received */
static int expected_base;                /* the next seqnum expected to be delivered */

/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
    struct pkt ack_pkt;
    int i;
    int seq = packet.seqnum;
    
    if (IsCorrupted(packet)) {
        if (TRACE > 0)
            printf("B: Corrupted packet received, discarded.\n");
        return;
    }

    /* check if the packet is in current window */
    if (((seq - expected_base + SEQSPACE) % SEQSPACE) < WINDOWSIZE) {
        if (!received[seq]) {
            recv_buffer[seq] = packet;
            received[seq] = true;

            if (TRACE > 0)
                printf("B: Packet %d received and buffered.\n", seq);
        } else {
            if (TRACE > 0)
                printf("B: Duplicate packet %d received, ACK resent.\n", seq);
        }

        /* send ACK back */
        ack_pkt.seqnum = 0;
        ack_pkt.acknum = seq;
        for (i = 0; i < 20; i++) ack_pkt.payload[i] = '0';
        ack_pkt.checksum = ComputeChecksum(ack_pkt);
        tolayer3(B, ack_pkt);

        /* try to deliver packets to application layer */
        while (received[expected_base]) {
            tolayer5(B, recv_buffer[expected_base].payload);
            packets_received++;
            received[expected_base] = false;
            expected_base = (expected_base + 1) % SEQSPACE;
        }

    } else {
        /* packet not in window, still send ACK */
        if (TRACE > 0)
            printf("B: Packet %d outside of window, ACK resent.\n", seq);

        ack_pkt.seqnum = 0;
        ack_pkt.acknum = seq;
        for (i = 0; i < 20; i++) ack_pkt.payload[i] = '0';
        ack_pkt.checksum = ComputeChecksum(ack_pkt);
        tolayer3(B, ack_pkt);
    }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
    int i;
    expected_base = 0;
    for (i = 0; i < SEQSPACE; i++) {
        received[i] = false;
    }
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}
