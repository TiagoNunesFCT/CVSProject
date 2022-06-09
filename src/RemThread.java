	//@ predicate RemThreadInv(RemThread RT;) = RT.loc_ccs |-> ?cc &*& cc != null &*& [_]CCSeqInv(cc);
public class RemThread implements Runnable {
    public CCSeq loc_ccs;



	//@ predicate pre() = RemThreadInv(this);
	//@ predicate post() = RemThreadInv(this);

	public RemThread(CCSeq ccs)
	//@ requires ccs != null &*& [?f]CCSeqInv(ccs);
	//@ ensures RemThreadInv(this);
	{
		loc_ccs = ccs;
	}

	public void run()
	//@ requires pre();
	//@ ensures post();
	{
		while (true)
		//@ invariant RemThreadInv(this);
		{
			for(int i = 0; i < 50; i++) {
			int v = loc_ccs.getCounter(i);
				if (v >= 0) {
					loc_ccs.remCounter(i);
				}
			}
		}
	}
    
}
