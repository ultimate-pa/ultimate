package local.stalin.interactiveconsole;

import java.util.List;


/**
 * Statement that is responsible for outputting a list of models stored in Stalin.
 * 
 * @author Christian Simon
 *
 */
public class ListMMStmt extends Stmt {

	@Override
	public void execute() {
		this.controller.updateModelList();
		List<String> modellist = this.controller.getModelList();
		System.out.println("Index\tDescription");
		for (int i=0; i<modellist.size(); i++) {
			System.out.println(String.valueOf(i)+"\t"+modellist.get(i));
		}
		
	}

}
