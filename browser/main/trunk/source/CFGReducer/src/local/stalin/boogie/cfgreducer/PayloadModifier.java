package local.stalin.boogie.cfgreducer;

import local.stalin.model.IAnnotations;
import local.stalin.model.IPayload;
import local.stalin.model.Payload;

public class PayloadModifier {

	public static Payload copyPayloadWithSSA(Payload payload){
		return copyPayload(payload, true);
	}
	
	public static Payload copyPayload(Payload payload){
		return copyPayload(payload, false);
	}
	
	public static Payload copyPayload(IPayload iPayload){
		return copyPayload((Payload)iPayload, false);
	}

	public static Payload copyPayloadWithSSA(IPayload iPayload){
		return copyPayload((Payload)iPayload, true);
	}
	
	private static Payload copyPayload(Payload payload, boolean useSSA){
		Payload newPayload = new Payload();
		for (String annotationsName: payload.getAnnotations().keySet()){
			IAnnotations annotations = payload.getAnnotations().get(annotationsName);
			if (annotationsName == "SMT"){
				IAnnotations newAnnotations = null;
				if (annotations instanceof SMTEdgeAnnotations){
					SMTEdgeAnnotations smtEdgeAnnotations = (SMTEdgeAnnotations)annotations;
					newAnnotations = useSSA? smtEdgeAnnotations.cloneSSA(): smtEdgeAnnotations.clone();
				} else if (annotations instanceof SMTNodeAnnotations){
					SMTNodeAnnotations smtNodeAnnotations = (SMTNodeAnnotations)annotations;
					newAnnotations = useSSA? smtNodeAnnotations.cloneSSA(): smtNodeAnnotations.clone();
				} else {
					newAnnotations = annotations;
				}
				newPayload.getAnnotations().put("SMT", newAnnotations);
			} else if (annotationsName == "SC"){
				continue;
			} else {
				newPayload.getAnnotations().put(annotationsName, annotations);
			}
		}
		newPayload.setLocation(payload.getLocation());
		newPayload.setName(payload.getName());
		
		return newPayload;
	}
}
