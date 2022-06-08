import java.util.concurrent.locks.*;


/*@
predicate_ctor CCSeqSharedState(CCSeq c) () = c.seq |-> ?s &*& s != null &*& CounterSeqInv(s,?cap, ?l) &*& l >= 0 &*& cap > 0 &*& l <= cap;
predicate_ctor CCSeqNotEmpty(CCSeq c) () = c.seq |-> ?s &*& CounterSeqInv(s,?cap, ?l) &*& l > 0 &*& cap > 0 &*& l <= cap;
predicate_ctor CCSeqNotFull(CCSeq c) () = c.seq |-> ?s &*& CounterSeqInv(s,?cap, ?l) &*& l < cap &*& cap > 0 &*& l >= 0;
predicate CCSeqInv(CCSeq c) = c.mon |-> ?l &*& l != null &*& lck(l,1, CCSeqSharedState(c)) 
	&*& c.notEmpty |-> ?ce &*& ce != null &*& cond(ce, CCSeqSharedState(c), CCSeqNotEmpty(c)) 
	&*& c.notFull |-> ?cf &*& cf != null &*& cond(cf, CCSeqSharedState(c), CCSeqNotFull(c));
@*/

public class CCSeq {
	
	CounterSequence seq;
	ReentrantLock mon;
	Condition notFull;
	Condition notEmpty;
	
	/*The constructor initializes a sequence with the given capacity.*/
	public CCSeq(int cap) 
	//@ requires cap > 0;
	//@ ensures CCSeqInv(this);
	{
		seq = new CounterSequence(cap);

		//@ close CCSeqSharedState(this)();
		//@ close enter_lck(1, CCSeqSharedState(this));
		mon = new ReentrantLock();
		
 		//@ close set_cond(CCSeqSharedState(this), CCSeqNotEmpty(this)); 
		notEmpty = mon.newCondition(); // notEmpty set to mean 0 < size <= cap

		//@ close set_cond(CCSeqSharedState(this), CCSeqNotFull(this));
		notFull = mon.newCondition(); // notFull set to mean 0 <= size < cap
		//@ close CCSeqInv(this);
	}
	
	
	/*The getCounter operation returns the value of the
	counter at position i, or -1 if that position is invalid.*/
	public int getCounter(int i) 
	//@ requires CCSeqInv(this);
	//@ ensures CCSeqInv(this);
	{	
		int ret = 0;
		
		//@ open CCSeqInv(this);
		mon.lock();
		//@ open CCSeqSharedState(this)();
		
		if(i < seq.length() && i >= 0) {
		//@ assert this.seq |-> ?s &*& CounterSeqInv(s, ?cap, ?l) &*& i < l;	
			
			ret = seq.getCounter(i);
			
		} else ret = -1;
		//@ close CCSeqSharedState(this)();
		mon.unlock();
		//@ close CCSeqInv(this);
		
		return ret;
	}
	
	
	/*Both incr and decr operations behave as before, 
	except the index i may not necessarily be a valid index in the sequence. 
	If i is not a valid index, the operations will return without modifying any counter in the sequence.*/
	public void incr(int i, int val) 
	//@ requires CCSeqInv(this);
	//@ ensures CCSeqInv(this);
	{
		mon.lock();
		if(i < seq.length() && i >= 0) {
		seq.increment(i, val);
		}
		mon.unlock();
	}
	
	public void decr(int i, int val) 
	//@ requires CCSeqInv(this);
	//@ ensures CCSeqInv(this);
	{
		mon.lock();
		if(i < seq.length() && i >= 0) {
		seq.decrement(i, val);
		}
		mon.unlock();
	}
	
	
	/*The addCounter operation will append a new counter (with the given limit) to the sequence,
	returning the index of the new counter. The insertion only takes place on a non-full sequence. (using concurrency mechanisms)*/
	public int addCounter(int limit) 
	//@ requires CCSeqInv(this);
	//@ ensures CCSeqInv(this);
	{	
		int index = -1;
		mon.lock();
		//@ open CCSeq_shared_state(this)();
		//Condition notFull
		while (seq.capacity() <= seq.length()) 
			/*@ invariant this.seq.length() |-> ?l
			&*& l >= 0
			&*& this.seq.capacity() |-> ?cap
			&*& cap > 0 
			&*& l <= cap
			&*& this.notEmpty |-> ?ce 
			&*& ce !=null
			&*& cond(ce, CCSeq_shared_state(this), CCSeq_notEmpty(this))
			&*& this.notFull |-> ?cf
			&*& cf !=null 
			&*& cond(cf, CCSeq_shared_state(this), CCSeq_notFull(this));
			@*/
		{
			//@close CCSeq_shared_state(this)();
			try { notFull.await(); } catch (InterruptedException e) {}
			//@ open CCSeq_notFull(this)();
		}
		index = seq.addCounter(limit);
		//@ close CCSeq_notEmpty(this)();
		notEmpty.signal();
		mon.unlock();
		return index;
	}
	
	/*The remCounter operation will remove the
	counter at the given index, or have no effect if the index does not contain a counter.
	The removal only takes place on a non-empty sequence. (using concurrency mechanisms)*/
	public void remCounter(int i)
	//@ requires CCSeqInv(this);
	//@ ensures CCSeqInv(this);
	{
		mon.lock();
		//@ open CCSeq_shared_state(this)();
		//Condition notEmpty
		while (0 >= seq.length()) 

		{ 
			//@close CCSeq_shared_state(this)();
			try { notEmpty.await(); } catch (InterruptedException e) {}
			//@ open CCSeq_notEmpty(this)();
		}
		seq.remCounter(i);
		//@ close CCSeq_notFull(this)();
		notFull.signal();
		//@ assert CCSeq_shared_state(this)();
		mon.unlock();
	}
	
	/* invariant this.N |-> ?v &*& v >= 0
	&*& this.MAX |-> ?m
	&*& m > 0 &*& v <= m
	&*& this.notzero |-> ?cc 
	&*& cc !=null
	&*& cond(cc,CCounter_shared_state(this), CCounter_nonzero(this))
	&*& this.notmax |-> ?cm
	&*& cm !=null 
	&*& cond(cm, CCounter_shared_state(this),CCounter_nonmax(this));
	*/
	
	/* CCounterInv(CCounter c) =
			c.mon |-> ?l
			&*& l != null
			&*& lck(l,1, CCounter_shared_state(c))
			&*& c.notzero |-> ?cc
			&*& cc != null
			&*& cond(cc, CCounter_shared_state(c), CCounter_nonzero(c))
			&*& c.notmax |-> ?cm
			&*& cm != null
			&*& cond(cm, CCounter_shared_state(c), CCounter_nonmax(c));
			*/
	
	/*Verification
	You will need to use the verification technique for monitors and conditions discussed in class
	to verify concurrent usages of the sequence. It will be convenient to define three predicate
	constructors: one for the shared sequence state and two specialized variants that relate to the
	conditions necessary to verify the operations of the sequence. You will also need to define the
	concurrent invariant, which specifies the memory layout of the concurrent sequence and the
	logical representation of any monitors and conditions. This invariant must be preserved by all
	the operations of the sequence.*/

}
