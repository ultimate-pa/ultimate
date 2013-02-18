package local.stalin.automata.petrinet.jan;

import local.stalin.automata.nwalibrary.ConcurrentProduct;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;

public class OperationsWithTests<S,C> {

	public boolean accepts(PetriNet<S,C> net, NestedWord<S> word) {
		NestedWordAutomaton<S,C> netAsAutomaton =
			(new PetriNet2FiniteAutomaton<S, C>(net)).getResult();
		boolean resultNet = net.accepts(word);
		boolean resultAutomaton = netAsAutomaton.accepts(word);
		assert (resultNet == resultAutomaton);
		return resultNet;	
	}
	
	
	public PetriNet<S,C> concurrentProduct(NestedWordAutomaton<S,C> nwa) {
		PetriNet<S,C> result = new PetriNet<S,C>(nwa, nwa.getContentFactory());
		NestedWordAutomaton<S,C> resultNetAsAutomaton =
			(new PetriNet2FiniteAutomaton<S,C>(result)).getResult();
		assert (resultNetAsAutomaton.equivalent(resultNetAsAutomaton, nwa));
		return result;
	}
	
	
	
	public PetriNet<S, C> concurrentProduct(PetriNet<S,C> net, 
									NestedWordAutomaton<S,C> nwa) {
		NestedWordAutomaton<S,C> netAsAutomaton =
			(new PetriNet2FiniteAutomaton<S, C>(net)).getResult();
		PetriNet<S,C> netResult = net.concurrentProduct(nwa);
		NestedWordAutomaton<S,C> resultNetAsAutomaton =
			(new PetriNet2FiniteAutomaton<S, C>(netResult)).getResult();
		NestedWordAutomaton<S,C> resultNwa = (NestedWordAutomaton<S, C>) 
			(new ConcurrentProduct(netAsAutomaton, nwa, false)).getResult();
		NestedRun<S,C> missingInResultNwa =
			resultNetAsAutomaton.included(resultNetAsAutomaton, resultNwa);
		NestedRun<S,C> missingInResultNet =
			resultNetAsAutomaton.included(resultNwa, resultNetAsAutomaton);
		assert (missingInResultNwa == null) : 
			"Only accepted by Net: " + missingInResultNwa;
		assert (missingInResultNet == null) : 
			"Only accepted by Nwa: " + missingInResultNet;
		assert (resultNetAsAutomaton.equivalent(resultNetAsAutomaton, resultNwa));
		return netResult;
	}
	
	
	public void prefixProduct(PetriNet<S,C> net, 
			NestedWordAutomaton<S,C> nwa) {
		NestedWordAutomaton<S,C> netAsAutomaton =
			(new PetriNet2FiniteAutomaton<S, C>(net)).getResult();
		net.prefixProduct(nwa);
		NestedWordAutomaton<S,C> resultNetAsAutomaton =
			(new PetriNet2FiniteAutomaton<S, C>(net)).getResult();
		NestedWordAutomaton<S,C> resultNwa = (NestedWordAutomaton<S, C>) 
		(new ConcurrentProduct(netAsAutomaton, nwa, true)).getResult();
		NestedRun<S,C> missingInResultNwa =
			resultNetAsAutomaton.included(resultNetAsAutomaton, resultNwa);
		NestedRun<S,C> missingInResultNet =
			resultNetAsAutomaton.included(resultNwa, resultNetAsAutomaton);
		assert (missingInResultNwa == null) : 
			"Only accepted by Net: " + missingInResultNwa;
		assert (missingInResultNet == null) : 
			"Only accepted by Nwa: " + missingInResultNet;

		assert (resultNetAsAutomaton.equivalent(resultNetAsAutomaton, resultNwa));		
	}
	
	
	
	public IPetriNetJan<S,C> selfloopIntersection(PetriNet<S,C> net, 
			NestedWordAutomaton<S,C> nwa) {
		NestedWordAutomaton<S,C> netAsAutomaton =
			(new PetriNet2FiniteAutomaton<S, C>(net)).getResult();
		IPetriNetJan<S,C> resultNet = 
			(new SelfloopIntersection<S,C>(net,nwa)).getResult();
		NestedWordAutomaton<S,C> resultNetAsAutomaton =
			(new PetriNet2FiniteAutomaton<S, C>(resultNet)).getResult();
		NestedWordAutomaton<S,C> resultNwa = (NestedWordAutomaton<S, C>) 
		(new ConcurrentProduct(netAsAutomaton, nwa, false)).getResult();
		NestedRun<S,C> missingInResultNwa =
			resultNetAsAutomaton.included(resultNetAsAutomaton, resultNwa);
		NestedRun<S,C> missingInResultNet =
			resultNetAsAutomaton.included(resultNwa, resultNetAsAutomaton);
		assert (missingInResultNwa == null) : 
			"Only accepted by Net: " + missingInResultNwa;
		assert (missingInResultNet == null) : 
			"Only accepted by Nwa: " + missingInResultNet;

		assert (resultNetAsAutomaton.equivalent(resultNetAsAutomaton, resultNwa));
		return resultNet;
	}
	
	
	
	public NestedRun<S,C> getAcceptingRun(PetriNet<S,C> net) {
		NestedRun<S,C> run = net.getAcceptedWord();
		NestedWordAutomaton<S,C> netAsAutomaton =
			(new PetriNet2FiniteAutomaton<S, C>(net)).getResult();
		if (run==null) {
			NestedRun<S,C> automatonRun = netAsAutomaton.getAcceptingNestedRun();
			assert (automatonRun == null);
			return null;
		}
		else {
			assert (net.accepts(run.getNestedWord()));
			assert (netAsAutomaton.accepts(run.getNestedWord()));
			return run;
		}
		
	}

//	public List<Collection<IPlace<S, C>>> getAcceptingRun(PetriNet<S,C> net) {
//	 List<Collection<IPlace<S, C>>> run = net.getAcceptedRun();
////	 = ((OccurrenceNet<S,C> ) 
////								net.getFinitePrefix()).getAcceptingRun();
//	NestedWordAutomaton<S,C> netAsAutomaton =
//		(new PetriNet2FiniteAutomaton<S, C>(net)).getResult();
//	if (run==null) {
//		NestedRun<S,C> automatonRun = netAsAutomaton.getAcceptingNestedRun();
//		assert (automatonRun == null);
//		return null;
//	}
//	else {
////		assert (net.accepts(run.getNestedWord()));
////		assert (netAsAutomaton.accepts(run.getNestedWord()));
//		return run;
//	}
	
	
}
