/*
 ______
/\__  _\
\/_/\ \/    __  __  __     __      ____     __     __  __  __     __
   \ \ \   /\ \/\ \/\ \  /'__`\   /',__\  /'__`\  /\ \/\ \/\ \  /'__`\
    \_\ \__\ \ \_/ \_/ \/\ \L\.\_/\__, `\/\ \L\.\_\ \ \_/ \_/ \/\ \L\.\_
    /\_____\\ \___x___/'\ \__/.\_\/\____/\ \__/.\_\\ \___x___/'\ \__/.\_\
    \/_____/ \/__//__/   \/__/\/_/\/___/  \/__/\/_/ \/__//__/   \/__/\/_/
*/
intrinsic RelativeClassNumber(m::RngIntElt) -> RngIntElt
  {given m defining QQ(zeta_m) return h^- the relative class number of QQ(zeta_m)}
  ZZ := IntegerRing();
  K := CyclotomicField(m);
  G := FullDirichletGroup(m);
  rel_class_num := 1;
  for i in {1..#Elements(G)} do
    chi := Elements(G)[i];
    if IsOdd(chi) then
      rel_class_num *:= (-1/2)*(Bernoulli(1, chi));
    end if;
  end for;
  rel_class_num *:= 2*m;
  if #Factorization(m) ne 1 then
    rel_class_num *:= 2;
  end if;
  return ZZ!rel_class_num;
end intrinsic;

intrinsic Lpn(i::RngIntElt, p::RngIntElt, n::RngIntElt, prec::RngIntElt) -> RngIntElt
  {Given i an integer such that ZZp!a is a unit in ZZp, p an odd prime, n a positive integer, and prec the working precision, return modified logarithm}
  ZZp := pAdicRing(p, prec);
  ZZ := IntegerRing();
  FFpn := FiniteField(p^n);
  val := ZZ!(FFpn!(ZZ!(Log(ZZp!(i))/p)));
  if val le ZZ!0 then
    return val;
  else
    return ZZ!(val-p^n);
  end if;
end intrinsic;

intrinsic LambdaChi(chi::GrpDrchElt, pp::RngOrdIdl, QQ_chi::FldCyc, z_chi::FldCycElt, p::RngIntElt, prec::RngIntElt) -> RngIntElt
  {returns lambda_chi for a particular chi...}
  ZZ := IntegerRing();
  ZK := Integers(QQ_chi);
  FFp := FiniteField(p);
  printf "\n  Taking chi = %o...\n",chi;
  P<T> := PolynomialRing(QQ_chi);
  f0 := Conductor(chi);
  for m in {0..(p-1)} do
    printf "    Computing coeff a_%o...",m;
    time1 := Cputime();
    coeff := 0;
    for i in {1..p^2} do
      if GreatestCommonDivisor(i, p) eq 1 then
        innersum := 0;
        for j in {0..(f0-1)} do
          innersum +:= j*chi(i+j*p^2);
        end for;
        binom :=  Binomial(-Lpn(i, p, 1, prec), m);
        innersum *:= binom;
        coeff +:= innersum;
      end if;
    end for;
    time2 := Cputime();
    printf "OK done. That took %o seconds.\n",time2-time1;
    printf "    coeff a_%o = %o\n",m,coeff;
    valuation := Valuation(coeff, pp);
    printf "    The valuation of coeff a_%o at pp equals %o.\n",m,valuation;
    if valuation eq 0 then
      printf "    Since ord_pp(a_%o) = %o, lambda_chi = %o.\n",m,valuation,m;
      return m;
    end if;
  end for;
end intrinsic;

intrinsic IwasawaLambda(p::RngIntElt, m::RngIntElt : prec := 20) -> RngIntElt
  {}
  ZZ := IntegerRing();
//  if m mod p eq 0 then
//    return "*";
//  end if;
  printf "\n\nChecking trivial cases...\n";
  printf "	Creating KK = CylotomicField(m)...\n";
  KK := CyclotomicField(m);
  printf "	Creating ZKK...\n";
  ZKK := Integers(KK);
  printf "	Factoring p in ZKK...\n";
  pFactorization := Factorization(p*ZKK);
  printf "	Computing RelativeClassNumber(m)...\n";
  rcn := RelativeClassNumber(m);
  if ((m mod 4) ne 2) and (#pFactorization eq 1) and ((rcn mod p) ne 0) then
    printf "\np = %o, m = %o, rcn = %o, #primes = %o\n",p,m,rcn,#pFactorization;
    printf "*";
    return ZZ!0;
  end if;
  printf "\n\nInitializing some values...\n";
  printf "  prec = %o.\n",prec;
  printf "  p = %o.\n",p;
  printf "  m = %o.\n",m;
  FFp := FiniteField(p);
  Gchi := FullDirichletGroup(m);
  chi := Elements(Gchi)[2];
  phi_chi := EulerPhi(m);
  printf "  Phi(m) = %o.\n",EulerPhi(m);
  printf "  Creating number field QQ(chi) and integers ZZ(chi)...";
  time4 := Cputime();
  QQ_chi<z_chi> := CyclotomicField(phi_chi);
  ZK := Integers(QQ_chi);
  time5 := Cputime();
  printf "OK done. That took %o seconds.\n",time5-time4;
  printf "  The characters chi are on Gal(QQ(zeta_%o)/QQ).\n",m;
  printf "    The conductor of each chi = %o.\n",Conductor(chi);
  printf "    Each chi takes values in the %o.\n",QQ_chi;
  printf "\n\n";
  all_chi_elts := Elements(Gchi);

  printf "First check that every character on Gal(QQ(zeta_%o)/QQ) is of the first kind for p...",m;
  for i in {1..#all_chi_elts} do
    if (Conductor(all_chi_elts[i]) mod p^2) eq 0 then
      printf "nope! returning *";
      return "*";
    end if;
  end for;
  printf "OK done.\n";

  printf "Now fix a (prime) ideal pp above p in QQ_chi...";
  time9 := Cputime();
  pp1 := Factorization(p*ZK)[1][1];
  time10 := Cputime();
  printf "OK done. That took %o seconds.\n",time10-time9;
  printf "We start by taking only the odd chi...they are\n";
  elts := [];
  for i in {1..#Gchi} do
    if IsOdd(all_chi_elts[i]) then
      Append(~elts,all_chi_elts[i]);
    end if;
  end for;
  printf "%o.\n\n\n",elts;
  lambda := 0;
  printf "Now compute lambda_chi for each of the above chi...\n\n";
  for i in {1..#elts} do
    val := LambdaChi(elts[i], pp1, QQ_chi, z_chi, p, prec);
    if Type(val) eq MonStgElt then
      return "**";
    end if;
    lambda +:= val;
    printf "  Therefore we add %o to IwasawaLambda to get %o thus far.",val,lambda;
  end for;
  printf "\n\n";
  printf "\n\n";
  printf "The Iwasawa lambda minus invariant for QQ(zeta_%o) and p = %o is %o.\n\n",m,p,lambda;
  return lambda;
end intrinsic;
