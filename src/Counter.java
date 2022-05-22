
public class Counter {
	
	/*current value, its upper-limit and a boolean flag that
	becomes true if the counter has ever over or underflowed its limit. 
	The limit is always a positive number.*/
	private int val;
	private int limit;
	private boolean overflow;
	
	
	public Counter(int val, int limit) 
	{
		this.val = val;
		this.limit = limit;
		overflow = false;
	}
	
	
	/*The get operations simply return the value of the counter and its limit.*/
	public int getVal() 
	{
		return val;
	}
	
	public int getLimit() 
	{
		return limit;
	}
	
	
	/*The modifier operations increment and decrement the counter, respectively. The value of the
	counter will always be between 0 (inclusive) and its upper-limit (non-inclusive).*/
	
	/*The increment operation,
	if the increment results in an overflow, will update the boolean flag accordingly
	and set the counter value modulo the limit.*/
	public void incr(int v) 
	{	
		val += v;
		if ((val > limit)) {
			val = val % limit;
			overflow = true;
		}
	}
	
	/*The decrement operation aims to decrement the counter value, 
	if the decrement would result in an underflow, 
	the operation updates the flag accordingly and sets the value to 0 instead. 
	If no underflow occurs, the decrement decreases the value of the counter as expected.*/
	public void decr(int v) 
	{
		val -= v;
		if ((val < 0)) {
			val = 0;
			overflow = true;
		}
	}

}
