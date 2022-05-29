
	/*@
		predicate CounterInv( Counter c; int v, int l, boolean o) =  c.val |-> v &*& c.limit |-> l &*& c.overflow |-> o &*& v >= 0 &*& l >= 0 &*& v < l;
	@*/

public class Counter {
	
	/*current value, its upper-limit and a boolean flag that
	becomes true if the counter has ever over or underflowed its limit. 
	The limit is always a positive number.*/
	private int val;
	private int limit;
	private boolean overflow;
	
	

	public Counter(int val, int limit)
	 //@ requires val >= 0 &*& limit > 0 &*& val < limit;
	 //@ ensures CounterInv(this, val, limit, false);
	{
		this.val = val;
		this.limit = limit;
		overflow = false;
	}
	
	
	/*The get operations simply return the value of the counter and its limit.*/
	public int getVal()
	//@ requires CounterInv(this, ?v, ?l, ?o);
	//@ensures CounterInv(this, v, l, o) &*& result==v; 
	{
		return val;
	}
	
	public int getLimit()
	//@ requires CounterInv(this, ?v, ?l, ?o);
	//@ensures CounterInv(this,v, l, o) &*& result==l;  
	{
		return limit;
	}
	
	
	/*The modifier operations increment and decrement the counter, respectively. The value of the
	counter will always be between 0 (inclusive) and its upper-limit (non-inclusive).*/
	
	/*The increment operation,
	if the increment results in an overflow, will update the boolean flag accordingly
	and set the counter value modulo the limit.*/
	public void incr(int v)
	//@ requires CounterInv(this, ?vv, ?l, ?o) &*& v >= 0;
	//@ ensures (vv+v >= l)? CounterInv(this, (vv+v)%l, l, true) : CounterInv(this, vv+v, l, o);
	{	
		val += v;
		if ((val >= limit)) {
			val = val % limit;
			overflow = true;
		}
	}
	
	/*The decrement operation aims to decrement the counter value, 
	if the decrement would result in an underflow, 
	the operation updates the flag accordingly and sets the value to 0 instead. 
	If no underflow occurs, the decrement decreases the value of the counter as expected.*/
	public void decr(int v) 
	//@ requires CounterInv(this, ?vv, ?l, ?o) &*& v >= 0;
	//@ ensures (vv-v < 0)? CounterInv(this, 0, l, true) : CounterInv(this, vv-v, l, o);
	{
		val -= v;
		if ((val < 0)) {
			val = 0;
			overflow = true;
		}
	}

}
