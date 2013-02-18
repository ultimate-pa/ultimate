package local.stalin.interactiveconsole;

import local.stalin.core.api.StalinServices;

/**
 * Statement that deals with deletion models from Stalin
 * 
 * @author Christian Simon
 *
 */
public class DeleteMMStmt extends Stmt {

	private int delete_idx;
	
	public DeleteMMStmt(String num) {
		this.delete_idx= Integer.valueOf(num);
	}
	
	@Override
	public void execute() {
		// get id of specified index
		String delete_item;
		try {
			delete_item = this.controller.getModelList().get(delete_idx);
		} catch (Exception e) {
			System.err.println("Unfortunately I couldn't identify model with specified index");
			System.err.println("Please make sure that you update your model list by running 'listmm' first");
			return;
		}
		
		boolean foo = StalinServices.getInstance().removeModel(delete_item);
		if (foo) {
			System.out.println("Model " + delete_item + " has been successfully removed.");
			this.controller.updateModelList();
		}
		else 
			System.err.println("Model " + delete_item + "couldn not be removed. Please update your model list using 'listmm'");
	}

}
