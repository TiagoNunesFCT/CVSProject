	//@ predicate AddthreadInv(AddThread AT;) = AT.loc_ccs |-> ?cc &*& cc != null &*& [_]CCSeqInv(cc);
public class AddThread implements Runnable {
	public CCSeq loc_ccs;


	//@ predicate pre() = AddthreadInv(this);
	//@ predicate post() = AddthreadInv(this);

	public AddThread(CCSeq ccs)
	//@ requires ccs != null &*& [1/2]CCSeqInv(ccs);
	//@ ensures AddThreadInv(this);
	{
		loc_ccs = ccs;
	}

	public void run()
	//@ requires pre();
	//@ ensures post();
	{
		while (true)
		//@ invariant AddThreadInv(this);
		{
			int i = loc_ccs.addCounter(10);
			loc_ccs.incr(i, 10);
			loc_ccs.decr(i, 10);
		}
	}

}
