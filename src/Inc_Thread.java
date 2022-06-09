public class Inc_Thread implements Runnable {
    public CCSeq loc_ccs;

    public Inc_Thread(CCSeq ccs) 
    //@ requires ccs != null &*& [1/2]CCSeqInv(cc)
    //@ ensures 
    {
        loc_ccs = ccs;
    }


    @Override
    public void run() {
        // TODO Auto-generated method stub
        
    }
    
}
