package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.NeverStatement;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;

public class BuchiProductObserver implements IUnmanagedObserver {


	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(IElement root) {
		
		
		
		if (root instanceof NeverStatement)
		{
			System.out.println("----------NEVER------------");
			//build and get automaton
			Never2Automaton nta = new Never2Automaton((AstNode)root);
			NestedWordAutomaton<AstNode,String> aut = nta.getAutomaton();
			
			List<String> modelDescs = UltimateServices.getInstance().getAllModels();
			for (String m: modelDescs)
			{
				GraphType gt = UltimateServices.getInstance().getGraphTypeFromStringModelId(m);
				System.out.println(gt.getFileNames());
			}
		}	
		if(root instanceof WrapperNode)
		{
			System.out.println("----------BOOGIE------------");
			
			return false;
		} else
			return true;
		
		
	}

}
