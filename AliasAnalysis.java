package submit_a1;



import java.util.*;

import dont_submit.AliasQuery;
import soot.Value;
import soot.JastAddJ.IfStmt;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PrimType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JInstanceFieldRef;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;


//-------Map for each unit in CFG-------------------
class State{
	
	public Map<String, Set<String>> stack;
    public Map<String, Set<String>> heap;
    
    public State() {
        stack = new HashMap<String, Set<String>>();
        heap = new HashMap<String, Set<String>>();
    }
    
    
    //------Check if two states are same-------------
    
    public boolean equals(State other) {
        // Check if the stack maps are equal
        if (!this.stack.equals(other.stack)) {
            return false;
        }
        
        // Check if the heap maps are equal
        if (!this.heap.equals(other.heap)) {
            return false;
        }
        
        // If both stack and heap maps are equal, return true
        return true;
    }
}


public class AliasAnalysis extends BodyTransformer{
	
	static int counter =0;
	static String obj = "O";
	static String global = "Og";
	
	public static void printState(State state) {
	    System.out.println("Stack:");
	    for (String key : state.stack.keySet()) {
	        System.out.print(key + ": { ");
	        for (String value : state.stack.get(key)) {
	            System.out.print(value + " ");
	        }
	        System.out.println("}");
	    }
	    
	    System.out.println("\nHeap:");
	    for (String key : state.heap.keySet()) {
	        System.out.print(key + ": { ");
	        for (String value : state.heap.get(key)) {
	            System.out.print(value + " ");
	        }
	        System.out.println("}");
	    }
	}
	
	
	//--------------------------MEET of Two State-----------------
	public static State merge(State s1, State s2) {
	    // Create a new state object to hold the merged state
	    State merged = new State();
	    
	    // Merge the stack maps
	    for (String key : s1.stack.keySet()) {
	        if (s2.stack.containsKey(key)) {
	            Set<String> unionSet = new HashSet<String>(s1.stack.get(key));
	            unionSet.addAll(s2.stack.get(key));
	            merged.stack.put(key, unionSet);
	        } else {
	            merged.stack.put(key, s1.stack.get(key));
	        }
	    }
	    for (String key : s2.stack.keySet()) {
	        if (!s1.stack.containsKey(key)) {
	            merged.stack.put(key, s2.stack.get(key));
	        }
	    }
	    
	    // Merge the heap maps
	    for (String key : s1.heap.keySet()) {
	        if (s2.heap.containsKey(key)) {
	            Set<String> unionSet = new HashSet<String>(s1.heap.get(key));
	            unionSet.addAll(s2.heap.get(key));
	            merged.heap.put(key, unionSet);
	        } else {
	            merged.heap.put(key, s1.heap.get(key));
	        }
	    }
	    for (String key : s2.heap.keySet()) {
	        if (!s1.heap.containsKey(key)) {
	            merged.heap.put(key, s2.heap.get(key));
	        }
	    }
	    
	    // Return the merged state object
	    return merged;
	}
	
	
	//-------------------WORKLIST ALGORITHM-------------------------------
	
	public static State worklist(UnitGraph g, Map<Unit,State> In) {
	    Set<Unit> visited = new HashSet<>();
	    Set<Unit> Workset = new HashSet<>();
	    Queue<Unit> worklist = new LinkedList<>();
	    
	    // Initialize the worklist with all nodes in the CFG
	    for (Unit u : g.getBody().getUnits()) {
	       State temp = new State();
	       In.put(u, temp);
	        worklist.offer(u);
	        Workset.add(u);
	    }
	    
	    
	    
	    
	    //--------Perform a BFS traversal of the CFG--------
	    
	    while (!worklist.isEmpty()) {
	    	
	    	State effect = new State();
		    State TotalEffect = new State();
	        Unit n = worklist.poll();
	        Workset.remove(n);
	       
	        List<Unit> Pred = g.getPredsOf(n);
	        
	        
	        if(Pred.size()==1){
	        	for(Unit P : Pred) {
	        		
	 	        	effect = Process(n,In.get(P),visited);
	 	        	TotalEffect.stack.putAll(effect.stack);
	 	        	TotalEffect.heap.putAll(effect.heap);
	 	        	
	 	        }
	        }
	        else{
	        	 for(Unit P : Pred) {
	        		

	 	        	effect = Process(n,In.get(P),visited);
	 	        	
	 	        	TotalEffect = merge(effect, TotalEffect);
	 	        	
	 	        }
	        }
	       
	       
	        if (!visited.contains(n)) {
	        	 visited.add(n);
	        }
	        

	        
	        // Add successors of the node to the worklist
	        if(!In.get(n).equals(TotalEffect)) {
	        	
	        	In.put(n, TotalEffect);
	        	 List<Unit> successors = g.getSuccsOf(n);
	 	        for (Unit succ : successors) {
	 	            	
	 	        		if(Workset.contains(succ)==false) {
	 	        			worklist.offer(succ);
	 	        			Workset.add(succ);
	 	        			
	 	        		}  
	 	        }
	        }
	        

	       
	    }
	    
	    State out=new State();
	    for(Unit u : visited) {
	    	
	    	if(g.getSuccsOf(u).size()==0) {
	    		out= In.get(u);
	    	}
	    }
	    
	    return out;
	}
	
		//----------------------Process each Unit--------------------------------
	
	public static State Process(Unit Node,State In,Set<Unit> visited) {
		
		
		State Out = new State();
		Out.stack.putAll(In.stack);
		Out.heap.putAll(In.heap);
		if((Node instanceof DefinitionStmt)) {
		DefinitionStmt defStmt = (DefinitionStmt) Node;
		Value L = defStmt.getLeftOp();
		Value R = defStmt.getRightOp();
		
		if (L instanceof Local && ((Local) L).getName().equals("this")) {
	        // Skip statements of the form "this := @this: P1"
			
	        return In;
	    }
		
		 
		else if (L.getType() instanceof PrimType) {
	        // Skip processing the statement, since the left-hand side is a primitive type
	        return In;
	    }
		else {
			
			if (L instanceof JInstanceFieldRef) {
		        // This is of the form X.f = Y
				
				
		       
		        
		         if (R instanceof Local) {
		        	// This is of the form X.f = Y
		    		
		    		
		    		InstanceFieldRef fieldRef = (InstanceFieldRef) L;
		    	    Value base = fieldRef.getBase();
		    	    SootField field = fieldRef.getField();
		    	    String Lvar = base.toString();
		    	    String fieldName = field.getName();
		    	    String Rvar = R.toString();
		    	    
		    	    // get values(reference) from stack of Y
		    	    Set<String> value = In.stack.get(Rvar);
		    	    
		    	    //get set of references from stack of X
		    	    Set<String> refs = In.stack.get(Lvar);
		    	    
		    	    //strong update
		    	    if(refs.size()<=1) {
		    	    	for(String ref : refs ) {
		    	    		Out.heap.put(ref+"."+fieldName, value);
		    	    	}
		    	    }
		    	    //weak update
		    	    else {
		    	    	for(String ref : refs ) {
		    	    		
		    	    		Out.heap.get(ref+"."+fieldName).addAll( value);
		    	    	}
		    	    }
		    	    	
		    	}
		        
		        
		        
		    } else if (L instanceof Local) {
		        
		    	
		    	if(R instanceof NewExpr) {
		    		// This is of the form X = new A();
					
					
					if(!visited.contains(Node)) {
						
						Set<String> set = new HashSet<>();
						
						String newObj =obj+Integer.toString(counter);
						set.add(newObj);
						counter++;
						
						Out.stack.put(L.toString(), set);
						
						 NewExpr newExpr = (NewExpr) R;
						    String className = newExpr.getBaseType().toString();

						    // Get the SootClass object for the class
						    SootClass cls = Scene.v().getSootClass(className);

						    // Get all the fields of the class
						    Chain<SootField> fields =  cls.getFields();
						    
						    //All fields to empty
						    for (SootField field : fields) {
						    	Set<String> temp = new HashSet<>();
						    	String fieldname = newObj+"." + field.getName();
						    	Out.heap.put(fieldname,temp);
						       
						    }
						    
						    
					}
							
				}
		    	else if (R instanceof FieldRef) {
		    		// This is of the form X = Y.f
		    		
		    	    if (R.toString().contains("<java.lang.System: java.io.PrintStream out>")) {
		    	        // Skip this DefinitionStmt
		    	        return Out;
		    	    }
		    		//separate variable name and field name from it
		    		
		    		
		    		
		    		InstanceFieldRef fieldRef = (InstanceFieldRef) R;
		    	    Value base = fieldRef.getBase();
		    	    SootField field = fieldRef.getField();
		    	    String variable = base.toString();
	    	    String fieldName = field.getName();
	    	    
	    	    
		    	    
		    	    //get set of ref from stack
		    	    
	    	    Set<String> ref = In.stack.get(variable);	
	    	    
//		    	    //get values for all references from heap
		    	    
	    	    Set<String> values = new HashSet<>();
	    	    for(String O : ref) {
	    	    	
	    	    	if(O.equals("Og")) {
	    	    		values.add("Og");
	    	    	}
	    	    	else if(In.heap.containsKey(O+"."+fieldName)==true) {
	    	    		
	    	    		values.addAll(In.heap.get(O+"."+fieldName));
	    	    	}
	    	    	
		    	    	
		    	    }
		    	    
		    	    Out.stack.put(L.toString(), values);
		    		
		    		
		    		 
		    	}
		    	
		    	//--------- X = Y -------------
		    	
		    	else if (R instanceof Local) {
		    		// This is of the form X = Y
		    
		    		
		    		Out.stack.put(String.valueOf(L), In.stack.get(R.toString()));
		    		
		    		
		    	}
		    	
		    	//----------Parameter to Function------------
		    	
		    	else if (R instanceof ParameterRef) {
		    		
		    		Set<String> ref = new HashSet<>();
		    		ref.add(global);
		    		
		    		//---Make Leftvar point to Og
		    		Out.stack.put(L.toString(), ref);
		    		
		    		//---Make fields of Leftvar point to Og
		    		Local obj = (Local) L;
		    		Type objType = obj.getType();
		    		SootClass objClass = ((RefType) objType).getSootClass();
		            Chain<SootField> fields = objClass.getFields();
		            
		            for(SootField f : fields) {
		            	Out.heap.put(global+"."+f.getName(), ref);
		            }
		    		
		    	}
		    	
		    	//------------X =A.foo(B)------------------
		    	
		    	else if (R instanceof InvokeExpr) {
		    		// This is of the form X = Y.fun()      
		    		
		    		InvokeExpr invokeExpr = (InvokeExpr) R;
		    		if(invokeExpr instanceof VirtualInvokeExpr) {
		    			//System.out.println("  function :- "+ defStmt.toString());
		    			
		    			//we dont know output of function so initialize with global object and make all fields to point global variable
		    			Set<String> val = new HashSet<>();
		    			val.add(global);
		    			Out.stack.put(L.toString(), val);
		    			Local obj = (Local) L;
			    		Type objType = obj.getType();
			    		SootClass objClass = ((RefType) objType).getSootClass();
			            Chain<SootField> fields = objClass.getFields();
			            
			            for(SootField f : fields) {
			            	Out.heap.put(global+"."+f.getName(), val);
			            }
		    			
		    			//need to set values of field of Y to global
		    			
		    			// Get the right-hand side expression of the DefinitionStmt
		    			InvokeExpr invokeExpr1 = (InvokeExpr) R;

		    			// Get the base of the invoke expression, which is the object invoking the method
		    			Value base = null;
		    			if (invokeExpr instanceof InstanceInvokeExpr) {
		    			    base = ((InstanceInvokeExpr) invokeExpr).getBase();
		    			}

		    			// Get the name of the object, if it is a local variable
		    			//System.out.print(base.toString());
		    			if (base instanceof Local && !base.toString().equals("this")) {
		    			    String objectName = ((Local) base).getName();
		    			    
		    			    Set<String> refrences = In.stack.get(objectName);
		    			    
		    			    for(String refField : In.heap.keySet()) {
		    			    	
		    			    	for(String ref : refrences) {
		    			    		if(refField.contains(ref)) {
		    			    			Out.heap.put(refField, val);
		    			    		}
		    			    	}
		    			    }
		    			}
		    			
		    			//Make all fields of references of argument passed to function to global(val)
		    			
		    			SootMethod method = invokeExpr.getMethod();
		    	        List<Value> arguments = invokeExpr.getArgs();
		    	        
		    	        for(Value arg : arguments) {
		    	        	
		    	        	Set<String> references = In.stack.get(arg.toString());
		    	        	
		    	        	for(String refField : In.heap.keySet()) {
		    			    	
		    			    	for(String ref : references) {
		    			    		if(refField.contains(ref)) {
		    			    			Out.heap.put(refField, val);
		    			    		}
		    			    	}
		    			    }
		    	        	
		    	        }
		    					
		    		}
		    		
		    	}
		    	
		    }
			
					
		    }
		}
		
		
		
		return Out;
		
	}

	
	//---------------------------Check if two variable are alias or not-------------
	public static boolean Alias(String var1, String var2, State out) {
	    Set<String> set1 = out.stack.get(var1);
	    Set<String> set2 = out.stack.get(var2);
	    
	    if (set1 == null || set2 == null) {
	        return false;
	    }
	    
	    if (set1.contains("Og") || set2.contains("Og")) {
	        return true;
	    }
	    
	    for (String ref : set1) {
	        if (!ref.equals("null") && set2.contains(ref)) {
	            return true;
	        }
	    }
	    
	    return false;
	}


	@Override
	protected void internalTransform(Body arg0, String arg1, Map<String, String> arg2) {
		/*
		 * Implement your alias analysis here. A1.answers should include the Yes/No answers for 
		 * the queries
		 */
		
		synchronized(arg0) {
			
			UnitGraph g = new BriefUnitGraph(arg0);
			
			if(arg0.getMethod().getName()!="<init>") {
				
//				
				Map<Unit,State> In = new HashMap<>();
				
				State out = worklist(g,In );
				
				
				
				for(int i=0;i<A1.queryList.size();i++) {
					AliasQuery q = A1.queryList.get(i);
					String className = q.getClassName();
					String Method = q.getMethodName();
			
					if(className.equals(arg0.getMethod().getDeclaringClass().toString()) && Method.equals(arg0.getMethod().getName())) {
						String var1 = q.getLeftVar() ,var2 = q.getRightVar();
						
						
						
						if(Alias(var1, var2, out)) {
							A1.answers[i]="Yes";
						}
						else {
							A1.answers[i]="No";
						}
					}
				}		
			}	
		}
   }
}
