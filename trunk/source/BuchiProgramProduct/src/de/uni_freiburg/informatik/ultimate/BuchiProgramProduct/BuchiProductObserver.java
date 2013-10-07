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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class BuchiProductObserver implements IUnmanagedObserver {
	
	private NestedWordAutomaton<ASTNode, String> aut = null; 
	private RootNode rcfg = null;
	
	public Product prod;


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
		if (this.aut != null && this.rcfg != null)
		{
			//TODO: product
			System.out.println("------------------PRODUCTCALC----------------------");
			
			try{
			this.prod = new Product(this.aut, this.rcfg);
			} catch (Exception e){
				System.out.println("ERROR:\n" + e.toString());
			}
			
			return false;
		}
		
		if (root instanceof NeverStatement &&  this.aut == null)
		{
			System.out.println("----------NEVER------------");
			//build and get automaton
			try{
			Never2Automaton nta = new Never2Automaton((AstNode)root);
			this.aut = nta.getAutomaton();
			}catch(Exception e){ 
				//TODO: log something
				System.out.println("ERROR:\n" + e.toString());
			}
			
			//GraphType modelDescs = UltimateServices.getInstance().;
			
		}	
		if(root instanceof RootNode && this.rcfg == null )
		{
			System.out.println("----------RootNode------------");
			this.rcfg = ((RootNode)root);
			
		} 
				
		return true;
		
		
	}

}
