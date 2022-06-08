/*@
predicate goodValuesNull(unit a, Counter c; unit n) = c == null &*& n == unit;
predicate goodValuesInv(unit a, Counter c; unit n) = c.val |-> ?v &*& c.limit |-> ?l &*& c.overflow |-> ?o &*& v >= 0 &*& l >= 0 &*& v < l &*& n == unit;
predicate Positive(unit a, int v; unit n) = v > 0 &*& n == unit;

predicate CounterSeqInv(CounterSequence s; int c, int sz) = s.cap |-> c &*& 
		s.size |-> sz &*&
		s.seq |-> ?sq &*& 
		sq != null &*& 
		sq.length == c &*&
		c >= sz &*&
		array_slice(sq,sz,c,_)&*&
		array_slice_deep(sq,0,sz,goodValuesInv, unit, _,_);
@*/


public class CounterSequence {

	private int cap;
	private int size;
	private Counter[] seq;
	
	/*The first constructor takes as a parameter the maximum capacity of the sequence,
	allocating memory accordingly and creating a sequence that has no counters.*/
	//array_slice_deep(o,0,o.length,goodValuesNull, unit, _, _); 

	public CounterSequence(int caps) 
	//@requires caps > 0;
	//@ensures CounterSeqInv(this,caps, 0);
	{
		this.cap = caps;
		size = 0;
		seq = new Counter[cap];
	}
	
	/*The second
	constructor takes as input an array of integers, with the intent of creating a sequence that
	will have as many counters as there are integers in the array*/
	public CounterSequence(int[] arr) 
	//@requires arr != null &*& arr.length > 0 &*& array_slice_deep(arr,0,arr.length, Positive, unit,_,_);
	//@ensures CounterSeqInv(this,arr.length, arr.length);
	{
		cap = arr.length;
		seq = new Counter[arr.length];
		
		for(int i = 0; i < arr.length; i++) 
		//@invariant array_slice_deep(arr,0,arr.length, Positive, unit,_,_) &*& i >= 0 &*& i <= arr.length &*& this.seq |-> ?sq &*& sq.length == arr.length &*& array_slice_deep(sq,0,i,goodValuesInv, unit, _,_) &*& array_slice(sq,i,arr.length,_);
		{
			seq[i] = new Counter(0, arr[i]);
		}
		size = arr.length;
	}
	
	
	/*The length and capacity methods return the current number of counters and the
	total capacity of the sequence, respectively.*/
	public int length() 
	//@requires CounterSeqInv(this,?a, ?l);
	//@ensures CounterSeqInv(this,a, l);

	{ 
		return size;
	}
	
	public int capacity() 
	//@requires CounterSeqInv(this,?a, ?l);
	//@ensures CounterSeqInv(this,a, l);
	{
		return cap;
	}

	
	/*The getCounter method returns the value of the
	counter in position i of the sequence.*/
	public int getCounter(int i) 
	//@requires CounterSeqInv(this,?a, ?l) &*& i < l &*& i >= 0;
	//@ensures CounterSeqInv(this,a, l) &*& result >= 0;
	{
		return seq[i].getVal();
	}
	
	
	/*The addCounter appends a new counter to the end of the sequence with upperlimit
	given the parameter limit, assuming the sequence is not at maximum capacity. The
	method returns the index of the added counter. New counters always start with value 0.*/
	public int addCounter(int limit) 	
	//@requires CounterSeqInv(this,?a, ?l) &*& a > l &*& limit > 0;
	//@ensures CounterSeqInv(this,a, l+1) &*& result == l;
	{	

			int oldSize = size;
			seq[size] = new Counter(0, limit);
			size++;
			return oldSize;
		
	}
	
	
	/*The
	two removal operations, remCounter and remCounterPO, both delete the counter at the
	given index of the sequence, assuming the index contains a counter.*/
	
	/*The remCounter operation is not order preserving,
	moving the last element of the sequence to the position of the removed counter.*/
	public void remCounter(int pos) 
	//@requires CounterSeqInv(this,?a, ?l) &*& a > l &*& l > 0 &*& l > pos &*& pos >= 0;
	//@ensures CounterSeqInv(this,a, l-1);
	{
			if(pos < size-1) {
			seq[pos] = seq[size-1];
			}
			else {			//estamos a remover o �ltimo da sequ�ncia
			seq[pos] = null;
			}
			size--;
		
	}
	
	/*The remCounterPO operation must preserve the order of the elements of
	the sequence (i.e. moving all appropriate counters accordingly).*/
	public void remCounterPO(int pos) 
	//@requires CounterSeqInv(this,?a, ?l) &*& a > l &*& l > 0 &*& l > pos &*& pos >= 0;
	//@ensures CounterSeqInv(this,a, l-1);
	{
			//@open CounterSeqInv(a, l);
			if(pos < size-1) {
			
			for(int i = pos; i < size-1; i++) 
			//@invariant cap |-> a &*& seq |-> ?sq &*& size |-> l &*& i >= pos &*& i <= l-1 &*& sq.length == a &*& array_slice_deep(sq,0,i,goodValuesInv, unit, _,_) &*& array_slice_deep(sq,i+1,l,goodValuesInv, unit, _,_) &*& array_element(sq, i, _) &*& array_slice(sq,l,a,_);
			{
				//seq[i] = seq[i+1];
				//seq[i+1] = null;
				Counter val = seq[i+1];
				seq[i+1] = null;
				seq[i] = val;
				
			}
			
			}else {				//estamos a remover o �ltimo da sequ�ncia
				seq[pos] = null;
			}
			size--;
			//@close CounterSeqInv(a, l-1);
	}
	
	
	/*The increment and decrement
	operations add and remove the given value to the counter in position i of the sequence. 
	These operations assume the given value is positive and i is a valid index.*/
	public void increment(int i, int val)
	//@requires CounterSeqInv(this,?a, ?l) &*& val > 0 &*& l > i &*& i >= 0;
	//@ensures CounterSeqInv(this,a, l);
	{
		seq[i].incr(val);
	}
	
	public void decrement(int i, int val) 
	//@requires CounterSeqInv(this,?a, ?l) &*& val > 0 &*& l > i &*& i >= 0;
	//@ensures CounterSeqInv(this,a, l);
	{
		seq[i].decr(val);
	}
	
	/*Verification
	Both classes must be accompanied with the appropriate predicates that characterize the memory
	footprint (and invariants) of their respective objects. All methods should have the appropriate
	pre-conditions, adhering to the informal but precise description above. In terms of postconditions,
	the Counter operations should precisely describe the changes to the Counter�s
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
