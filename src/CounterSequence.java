
public class CounterSequence {

	
	/*The first constructor takes as a parameter the maximum capacity of the sequence,
	allocating memory accordingly and creating a sequence that has no counters.*/
	public CounterSequence(int cap) 
	{
		
	}
	
	/*The second
	constructor takes as input an array of integers, with the intent of creating a sequence that
	will have as many counters as there are integers in the array*/
	public CounterSequence(int[] arr) 
	{
		
	}
	
	
	/*The length and capacity methods return the current number of counters and the
	total capacity of the sequence, respectively.*/
	public int length() 
	{ 
		return 0; 
	}
	
	public int capacity() 
	{
		return 0;
	}

	
	/*The getCounter method returns the value of the
	counter in position i of the sequence.*/
	public int getCounter(int i) 
	{
		return 0;
	}
	
	
	/*The addCounter appends a new counter to the end of the sequence with upperlimit
	given the parameter limit, assuming the sequence is not at maximum capacity. The
	method returns the index of the added counter. New counters always start with value 0.*/
	public int addCounter(int limit) 
	{
		return 0;
	}
	
	
	/*The
	two removal operations, remCounter and remCounterPO, both delete the counter at the
	given index of the sequence, assuming the index contains a counter.*/
	
	/*The remCounter operation is not order preserving,
	moving the last element of the sequence to the position of the removed counter.*/
	public void remCounter(int pos) 
	{
		
	}
	
	/*The remCounterPO operation must preserve the order of the elements of
	the sequence (i.e. moving all appropriate counters accordingly).*/
	public void remCounterPO(int pos) 
	{
		
	}
	
	
	/*The increment and decrement
	operations add and remove the given value to the counter in position i of the sequence. 
	These operations assume the given value is positive and i is a valid index.*/
	public void increment(int i, int val) 
	{
		
	}
	
	public void decrement(int i, int val) 
	{
		
	}
	
	/*Verification
	Both classes must be accompanied with the appropriate predicates that characterize the memory
	footprint (and invariants) of their respective objects. All methods should have the appropriate
	pre-conditions, adhering to the informal but precise description above. In terms of postconditions,
	the Counter operations should precisely describe the changes to the Counter’s
	internal state (i.e., of its value and the flag), following the description of the modifier operations
	given above.
	The CounterSequence operations, as a result of the predicate-based verification, need
	only visibly capture the number of elements of the sequence and its capacity. This means that
	the operations that add or remove counters from the sequence should have post-conditions that
	track this fact accordingly. The lookup operation need only additionally ensure that its result
	is non-negative (i.e., you need not verify that the result is within the upper-bound of the corresponding
	counter).
	Important Note: The class invariant for the sequence should maintain the fact that all stored
	counter objects are correct (i.e., their values are between 0 and their upper-limits). This will
	require characterizing the array via the array_slice_deep predicate (up to the number of
	stored counters) and the array_slice predicate (for the null positions at the end of the
	sequence).*/
	
}
