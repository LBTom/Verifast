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

class Travailleur{

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
}
```  
### Question 4
```
/*@
predicate travailleur(Travailleur travailleur;int temps_dispo, int salaire_horaire, int salaire_percu) = 
	  travailleur.temps_dispo |-> temps_dispo &*& travailleur.salaire_horaire |-> salaire_horaire &*& travailleur.salaire_percu |-> salaire_percu &*&
	  temps_dispo>=0 &*& 
	  salaire_horaire >= 0 &*& 
	  salaire_percu>=0;
@*/
class Travailleur
{
	private int temps_dispo;
	
	private int salaire_horaire;
	
	private int salaire_percu;

	public Travailleur(int t,int s)
	//@requires t>=0 && s >=0;
	//@ensures travailleur(this,t,s,0); 
	{
		this.temps_dispo = t;
		this.salaire_horaire = s;
		this.salaire_percu = 0;
	}
	
	public int get_temps_dispo()
	//@requires travailleur(this,?temps_dispo,?salaire_horaire,?salaire_percu);
	//@ensures travailleur(this, temps_dispo, salaire_horaire, salaire_percu) &*& result == temps_dispo;
	{
		return this.temps_dispo;
	}
	
	public int get_salaire_horaire()
	//@requires travailleur(this, ?temps_dispo, ?salaire_horaire, ?salaire_percu);
	//@ensures travailleur(this, temps_dispo, salaire_horaire, salaire_percu) &*& result == salaire_horaire;
	{
		return this.salaire_horaire;
	}
	
	public int get_salaire_percu()
	//@requires travailleur(this, ?temps_dispo, ?salaire_horaire, ?salaire_percu);
	//@ensures travailleur(this, temps_dispo, salaire_horaire, salaire_percu) &*& result == salaire_percu;
	{
		return this.salaire_percu;
	}
	
	public int travailler(int t)
	/*@requires travailleur(this, ?temps_dispo, ?salaire_horaire, ?salaire_percu) &*& 
		    t > 0 &*& 
		    t <= temps_dispo &*&
		    salaire_percu + (t *salaire_horaire)>=0;
	@*/
	
	/*@ensures travailleur(this, temps_dispo-t, salaire_horaire, (salaire_percu + (t * salaire_horaire))) &*& 
		   result == (t * salaire_horaire);
	@*/
	{
		this.salaire_percu = this.salaire_percu + (t * this.salaire_horaire);
		this.temps_dispo = this.temps_dispo - t;
		return (t*this.salaire_horaire);
	}
}

```  

### Question 5

```  
public int travailler(int t)
/*@requires travailleur(this, ?temps_dispo, ?salaire_horaire, ?salaire_percu) &*& 
	    t > 0 &*& 
	    t <= temps_dispo &*&
	    salaire_percu + (t *salaire_horaire)>=0;
@*/	
/*@ensures travailleur(this, temps_dispo-t, salaire_horaire, (salaire_percu + (t * salaire_horaire))) &*& 
	   result == (t * salaire_horaire);
@*/
{
	this.salaire_percu = this.salaire_percu + (t * this.salaire_horaire);
	this.temps_dispo = this.temps_dispo - t;
	return (t*this.salaire_horaire);
}
	
```  

### Question 6 


répondre à question

### Question 7









