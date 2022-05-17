
public class CCSeq {
	
	CounterSequence seq;
	//Other relevant fields go here...
	
	
	/*The constructor initializes a sequence with the given capacity.*/
	public CCSeq(int cap) 
	{
		
	}
	
	
	/*The getCounter operation returns the value of the
	counter at position i, or -1 if that position is invalid.*/
	public int getCounter(int i) 
	{
		return 0;
	}
	
	
	/*Both incr and decr operations behave as before, 
	except the index i may not necessarily be a valid index in the sequence. 
	If i is not a valid index, the operations will return without modifying any counter in the sequence.*/
	public void incr(int i, int val) 
	{
		
	}
	
	public void decr(int i, int val) 
	{
		
	}
	
	
	/*The addCounter operation will append a new counter (with the given limit) to the sequence,
	returning the index of the new counter. The insertion only takes place on a non-full sequence. (using concurrency mechanisms)*/
	public int addCounter(int limit) 
	{
		return 0;
	}
	
	/*The remCounter operation will remove the
	counter at the given index, or have no effect if the index does not contain a counter.
	The removal only takes place on a non-empty sequence. (using concurrency mechanisms)*/
	public void remCounter(int i) 
	{
		
	}
	
	
	/*Verification
	You will need to use the verification technique for monitors and conditions discussed in class
	to verify concurrent usages of the sequence. It will be convenient to define three predicate
	constructors: one for the shared sequence state and two specialized variants that relate to the
	conditions necessary to verify the operations of the sequence. You will also need to define the
	concurrent invariant, which specifies the memory layout of the concurrent sequence and the
	logical representation of any monitors and conditions. This invariant must be preserved by all
	the operations of the sequence.*/

}
