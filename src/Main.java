import java.util.concurrent.*;
import java.util.concurrent.locks.*;

public class Main {

	
	/*A client that launches 100 threads to: 
	(a) add counters and perform increment/decrements to the added counter;
	(b) query a counter�s value and remove it from the sequence, printing a log on the standard output. 
	The threads that perform (a) should run concurrently with those that perform (b).*/
	public static void main(String[] args) {
        CCSeq cSeq = new CCSeq(10);
        //@ assert CCSeqInv(cSeq);
        for(int i = 0; i < 100; i++) 
        //@ invariant [?f]CCSeqInv(cSeq);
        {
            //@ close [f/2]CCSeqInv(cSeq);
            new Thread(new Inc_thread(cSeq)).start();
            //@ close [f/4]CCSeqInv(cSeq);
            new Thread(new Get_Removethread(cSeq)).start();
            //@ close [f/4]CCSeqInv(cSeq);
        }
    
    }

}
