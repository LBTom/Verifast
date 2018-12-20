/*@predicate tache(Tache tache; int temps_necessaire, int gain) = 
	tache.temps_necessaire |-> temps_necessaire &*& 
	tache.gain |-> gain &*&
	temps_necessaire > 0 &*& 
	gain > 0; 

@*/
class Tache
{

	private int temps_necessaire;
	
	private int gain;
	
	public Tache(int t,int g)
	//@requires t>0 && g>0;
	//@ensures tache(this, t, g);
	{
		this.temps_necessaire = t;
		this.gain = g;
	}
	
	public int get_gain()
	//@requires tache(this, ?temps_necessaire,?gain);
	//@ensures tache(this, temps_necessaire, gain) &*& result == gain;
	{
		return this.gain;
	}
	
	public int get_temps_necessaire()
	//@requires tache(this, ?temps_necessaire, ?gain);
	//@ensures tache(this, temps_necessaire, gain) &*& result == temps_necessaire;
	{
		return this.temps_necessaire;
	}
}