package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.NeverStatement;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class BuchiProductObserver implements IUnmanagedObserver {
	
	private NestedWordAutomaton<BoogieASTNode, String> automaton = null; 
	private RootNode rcfg = null;
	
	public Product product;


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
	/**
	 * Collect one RCFG and one LTL2Aut.AST and execute the product 
	 * algorithm on them.
	 */
	public boolean process(IElement root) {
		
		//if everything is found, execute produrct
		if (this.automaton != null && this.rcfg != null)
		{
			System.out.println("------------------PRODUCTCALC----------------------");
			
			try{
				this.product = new Product(this.automaton, this.rcfg);
			} catch (Exception e){
				//TODO: log something
				System.out.println("ERROR:\n" + e.toString());
			}
			
			return false;
		}

		
		//collect root nodes of Buechi automaton
		if (root instanceof NeverStatement &&  this.automaton == null)
		{
			System.out.println("----------NEVER------------");
			//build and get automaton
			try{
				Never2Automaton nta = new Never2Automaton((AstNode)root);
				this.automaton = nta.getAutomaton();
			}catch(Exception e){ 
				//TODO: log something
				System.out.println("ERROR:\n" + e.toString());
			}
			
		}
		//collect root node of program's RCFG
		if(root instanceof RootNode && this.rcfg == null )
		{
			System.out.println("----------RootNode------------");
			this.rcfg = ((RootNode)root);
			
		} 
				
		return true;
		
		
	}

}
