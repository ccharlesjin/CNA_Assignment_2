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
#define SEQSPACE 13    /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */
/* extern float time; */
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

static struct pkt buffer[SEQSPACE];     /* array for storing packets waiting for ACK */
static bool acked [SEQSPACE];           /* mark whether each packet in window is acked */
static int base;                        /* base of the window */
static int nextseqnum;                  /* sequence number for next packet to send */
static float sent_time[SEQSPACE];       /* last sent time for each packet */
bool timer_running = false;

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{   
    int i;
    struct pkt sendpkt;
    /* put message into local buffer first */
    if ( (nextseqnum + SEQSPACE - base) % SEQSPACE >= WINDOWSIZE ) {
        if (TRACE > 0)
            printf("----A: New message arrives, send window is full\n");
        window_full++;
        return;
    }
    if (TRACE > 1)
        printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");
    
    /* make a packet */
    sendpkt.seqnum = nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for (i = 0; i < 20; ++i)
        sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* send to layer 3 */
    if (TRACE > 0)
        printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3(A, sendpkt);

    buffer[nextseqnum] = sendpkt;
    acked [nextseqnum] = false;
    sent_time[nextseqnum] = 1;
    /* start timer if it is the first packet */
    if (!timer_running){
        starttimer(A, RTT);
        timer_running = true;
    }
    nextseqnum = (nextseqnum + 1) % SEQSPACE;
}


/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{   
    int ack = packet.acknum;
    int diff = (ack - base + SEQSPACE) % SEQSPACE;
    bool has_unacked = false;
    int i;
    /* Filtering emulator corruption */
    if (ack < 0 || ack >= SEQSPACE){
        return;
    }
    if (IsCorrupted(packet)) {
        if (TRACE > 0)
            printf("----A: corrupted ACK is received, do nothing!\n");
        return; 
    }
    
    if (TRACE > 0) printf("----A: uncorrupted ACK %d is received\n", ack);
    total_ACKs_received++;
    if (diff >= WINDOWSIZE) {
        return;  /* already marked ACK, do nothing */
    }

    /*  ignore ACK if it is not in window */

    /* mark the seq as confirmed */
    if (!acked[ack]) {
        if (TRACE > 0) printf("----A: ACK %d is not a duplicate\n", ack);
        new_ACKs++;
        acked[ack] = true;
        sent_time[ack] = -1.0;
    }

    while (acked[base]) {
        acked[base] = false;
        base = (base + 1) % SEQSPACE;
    }

    for (i = 0; i < WINDOWSIZE; i++) {
        int seq = (base + i) % SEQSPACE;
        if (!acked[seq] && sent_time[seq] != -1.0) {
            has_unacked = true;
            break;
        }
    }

    if (has_unacked) {
    if (timer_running) stoptimer(A);
    starttimer(A, RTT);
    timer_running = true;
} else {
    if (timer_running) stoptimer(A);
    timer_running = false;
}
}


/* called when A's timer goes off */
void A_timerinterrupt(void)
{   
    bool has_unacked = false;
    int i;
    /* float now = time; */
    if (TRACE > 0){
        printf("----A: time out,resend packets!\n");
    }

    for (i = 0; i < WINDOWSIZE; i++) {
        int seq = (base + i) % SEQSPACE;
        if (!acked[seq] && sent_time[seq] != -1.0) {
            tolayer3(A, buffer[seq]);  /* resend all not ACKed packets */
            packets_resent++;
            if (TRACE > 0){
                printf ("---A: resending packet %d\n", seq);
            }
            break;
        }
    }
    for (i = 0; i < WINDOWSIZE; i++) {
        int seq = (base + i) % SEQSPACE;
        if (!acked[seq] && sent_time[seq] != -1.0) {
            has_unacked = true;
            break;
        }
    }
    if (has_unacked) {
        starttimer(A, RTT);
        timer_running = true;
    } else {
        timer_running = false;
    }
}


/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
    int i;
    base = 0;
    nextseqnum = 0;
    for (i = 0; i < SEQSPACE; i++) {
        acked[i] = false;
        sent_time[i] = -1.0;
    }
}


/********* Receiver (B)  variables and procedures ************/

static struct pkt recv_buffer[SEQSPACE]; /* buffer to store received packets */
static bool received[SEQSPACE];          /* mark if a packet has been received */
static int expected_base = 0;                /* the next seqnum expected to be delivered */
static int last_ack_sent = -1;
/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
    struct pkt ack_pkt;
    int seq = packet.seqnum;
    int i;
    bool corrupted = IsCorrupted(packet);
    int distance = (seq - expected_base + SEQSPACE) % SEQSPACE;
    /* Always ACK the received packet, even if corrupted or duplicate */
    ack_pkt.seqnum = 0;
    /* Filtering corruption pkg */
    printf("B: 收到包！seq：%d\n", seq);
    if (seq < 0 || seq >= SEQSPACE) {
        return;
    }
    for (i = 0; i < 20; i++) ack_pkt.payload[i] = '0';
    printf("corrupted: %d, seq: %d, expected_base: %d, SEQSPACE: %d, last_ack_sent: %d\n", corrupted, seq, expected_base, SEQSPACE, last_ack_sent);
    if (!corrupted && distance < WINDOWSIZE) {
        if (!received[seq]) {
            recv_buffer[seq] = packet;
            received[seq] = true;
            last_ack_sent = seq;
            if (TRACE > 0)
                printf("----B: packet %d is correctly received, send ACK!\n", seq);
        }

        /* deliver in-order */
        while (received[expected_base]) {
            tolayer5(B, recv_buffer[expected_base].payload);
            packets_received++;
            received[expected_base] = false;
            expected_base = (expected_base + 1) % SEQSPACE;
        }

        ack_pkt.acknum = seq;
    } else if (distance >= SEQSPACE / 2) {
        /* past packet */
        ack_pkt.acknum = seq;  /*  do not receive but send ack */
        /* last_ack_sent = seq; */
    } else {
        /* If corrupted or duplicate/invalid, resend last ACK */
        if (last_ack_sent == - 1) {
            return;
        } else {
            ack_pkt.acknum = last_ack_sent;
        }
        if (TRACE > 0)
            printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");
    }

    ack_pkt.checksum = ComputeChecksum(ack_pkt);
    /* last_ack_sent = ack_pkt.acknum;  */    /* save the lastest ACK */
    tolayer3(B, ack_pkt);
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
