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
static int base;                        /* base of the window */
static int nextseqnum;                  /* sequence number for next packet to send */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
    struct pkt sendpkt;
    int i;

    if ((nextseqnum + SEQSPACE - base) % SEQSPACE < WINDOWSIZE) {
        if (TRACE > 1)
            printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");
        
        /* create packet */
        sendpkt.seqnum = nextseqnum;
        sendpkt.acknum = NOTINUSE;
        for (i = 0; i < 20; i++)
            sendpkt.payload[i] = message.data[i];
        sendpkt.checksum = ComputeChecksum(sendpkt);

        /* send packet to layer 3 */
        if (TRACE > 0)
            printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
        tolayer3(A, sendpkt);

        /* save to buffer */
        buffer[nextseqnum % WINDOWSIZE] = sendpkt;
        acked[nextseqnum % WINDOWSIZE] = false;

        if (base == nextseqnum) {
            starttimer(A, RTT);
        }

        nextseqnum = (nextseqnum + 1) % SEQSPACE;
    } else {
        if (TRACE > 0)
            printf("----A: New message arrives, send window is full\n");
        window_full++;
    }
}


/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{
    int acknum;
    int index;

    if (!IsCorrupted(packet)) {
        acknum = packet.acknum;

        if (TRACE > 0)
            printf("----A: uncorrupted ACK %d is received\n", acknum);

        total_ACKs_received++;

        /* check if new ACK (in window and not duplicate) */
        if (((base <= acknum) && (acknum < nextseqnum)) ||
            ((base > nextseqnum) && (acknum < nextseqnum || acknum >= base))) {

            if (!acked[acknum % WINDOWSIZE]) {
                if (TRACE > 0)
                    printf("----A: ACK %d is not a duplicate\n", acknum);

                new_ACKs++;
                index = acknum % WINDOWSIZE;
                acked[index] = true;

                /* try to slide window forward */
                while (acked[base % WINDOWSIZE]) {
                    acked[base % WINDOWSIZE] = false;

                    if (TRACE > 0)
                        printf("----A: sliding window, base %d now\n", base);

                    base = (base + 1) % SEQSPACE;

                    stoptimer(A);
                    if (base != nextseqnum)
                        starttimer(A, RTT);
                }
            } else {
                if (TRACE > 0)
                    printf("----A: duplicate ACK received, do nothing!\n");
            }

        } else {
            if (TRACE > 0)
                printf("----A: duplicate ACK received, do nothing!\n");
        }

    } else {
        if (TRACE > 0)
            printf("----A: corrupted ACK is received, do nothing!\n");
    }
}





/* called when A's timer goes off */
void A_timerinterrupt(void)
{
    int i = base;
    
    if (TRACE > 0)
        printf("----A: time out,resend packets!\n");

    while (i != nextseqnum) {
        if (TRACE > 0)
            printf("---A: resending packet %d\n", buffer[i % WINDOWSIZE].seqnum);

        tolayer3(A, buffer[i % WINDOWSIZE]);
        packets_resent++;
        i = (i + 1) % SEQSPACE;
    }

    starttimer(A, RTT);
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
            printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");
        return;
    }

    /* check if the packet is in current window */
    if (((seq - expected_base + SEQSPACE) % SEQSPACE) < WINDOWSIZE) {
        if (!received[seq]) {
            recv_buffer[seq] = packet;
            received[seq] = true;

            if (TRACE > 0)
                printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
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
