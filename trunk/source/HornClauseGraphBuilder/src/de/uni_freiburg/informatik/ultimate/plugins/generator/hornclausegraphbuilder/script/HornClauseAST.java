package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.script;


import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;

public class HornClauseAST implements IElement {

	Payload payload;
	public HornClauseAST(Payload payload) {
		this.payload = payload;
	}
	@Override
	public IPayload getPayload() {
		return payload;
	}

	@Override
	public boolean hasPayload() {
		return payload != null;
	}

}
