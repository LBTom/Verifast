# Projet Verifast
## Auteur
Tom LE BERRE
Nicolas VANNIER


### Question 1
```  
class Tache{

	private int temps_necessaire;
	private int gain;

	public Tache(int t,int g)	{
		this.temps_necessaire = t;
		this.gain = g;
	}

	public int get_gain()	{
		return this.gain;
	}

	public int get_temps_necessaire()	{
		return this.temps_necessaire;
	}
} 
```

### Question 2
```  
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
```  

### Question 3
```  
class Travailleur
{
	private int temps_dispo;
	private int salaire_horaire;
	private int salaire_percu;

	public Travailleur(int t,int s){
		this.temps_dispo = t;
		this.salaire_horaire = s;
		this.salaire_percu = 0;
	}
	
	public int get_temps_dispo()	{
		return this.temps_dispo;
	}
	
	public int get_salaire_horaire(){
		return this.salaire_horaire;
	}
	
	public int get_salaire_percu(){
		return this.salaire_percu;
	}
```  
