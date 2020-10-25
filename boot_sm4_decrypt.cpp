#include <iostream>

#include <helib/helib.h>
#include <helib/intraSlot.h>
#include <NTL/vector.h>
#include <helib/permutations.h>
#include "originsm4.h"

#define PolyType helib::DoubleCRT

void invertSingle(helib::Ctxt& ctxt) {
    helib::Ctxt tmp1(ctxt);           // tmp1   = data[i] = X
    tmp1.frobeniusAutomorph(1);   // tmp1   = X^2   after Z -> Z^2
    ctxt.multiplyBy(tmp1);     // data[i]= X^3
    helib::Ctxt tmp2(ctxt);           // tmp2   = X^3
    tmp2.frobeniusAutomorph(2);   // tmp2   = X^12  after Z -> Z^4
    tmp1.multiplyBy(tmp2);        // tmp1   = X^14
    ctxt.multiplyBy(tmp2);     // data[i]= X^15
    ctxt.frobeniusAutomorph(4);// data[i]= X^240 after Z -> Z^16
    ctxt.multiplyBy(tmp1);     // data[i]= X^254
}
// the transformation X -> X^{-1} in GF(2^8)
void invert(std::vector<helib::Ctxt>& data)
{
  for (long i=0; i<(long)data.size(); i++){ // compute X -> X^{254} on i'th ctxt
    invertSingle(data[i]);
  }
}
void buildAffine(std::vector<PolyType>& binMat, PolyType* binVec,
			const unsigned char cc[],
			const helib::EncryptedArrayDerived<helib::PA_GF2>& ea2)
{
  std::vector<NTL::GF2X> scratch(8); // Specify the different columns
  for (long j = 0; j < 8; j++) // convert from byte to degree-7 polynomial
    GF2XFromBytes(scratch[j], &cc[j], 1);

  // "building" the linearized-polynomial coefficients
  std::vector<NTL::GF2X> C;
  ea2.buildLinPolyCoeffs(C, scratch);

  // "encoding" the coefficients
  std::vector<NTL::ZZX> zzxMat;

  zzxMat.resize(8);
  scratch.resize(ea2.size());
  for (long j = 0; j < 8; j++) {
    for (long i = 0; i < ea2.size(); i++) // set all slots to C[j]
      scratch[i] = C[j];
    ea2.encode(zzxMat[j], scratch);       // encode these slots
  }

  binMat.resize(8,helib::DoubleCRT(ea2.getContext(), ea2.getContext().ctxtPrimes | ea2.getContext().specialPrimes ));
  for (long j=0; j<8; j++) binMat[j] = zzxMat[j];

  if (binVec != NULL) {
    NTL::GF2X cc8;
    GF2XFromBytes(cc8, &cc[8], 1);
    for (long i = 0; i < ea2.size(); i++)  // set all slots to cc8
      scratch[i] = cc8;

    NTL::ZZX tmpZZX;
    ea2.encode(tmpZZX, scratch);        // encode these slots
    *binVec = tmpZZX;                   // conveer to DoubleCRT
  }
}

void setPackingConstants(NTL::GF2X& XinSlots, NTL::Mat<NTL::GF2X>& unpacking, helib::EncryptedArrayDerived<helib::PA_GF2>& ea2)
{
  // Get the context and the ea for "fully packed" polynomials
  const helib::Context& context = ea2.getContext();
  const helib::EncryptedArrayDerived<helib::PA_GF2>& ea = context.ea->getDerived(helib::PA_GF2());

  // Compute the packing constants, with X in all the slots
  {std::vector<NTL::GF2X> slots(ea.size(), NTL::GF2X(1,1)); // X in all the slots
  NTL::ZZX tmp; ea.encode(tmp, slots); // encode as ZZX
  NTL::conv(XinSlots, tmp);}           // convert to ZZ2X

  // Compute the unpacking constants

  long e = ea.getDegree() / 8; // the extension degree

  NTL::GF2EBak bak; bak.save(); // save current modulus (if any)
  NTL::GF2XModulus F0(ea.getTab().getFactors()[0]);
  NTL::GF2E::init(F0);

  // Set a matrix for converting from z = sum_i zi*X^i in GF(2^d)
  // back to the vectors of zi's in GF(2^8)

  NTL::mat_GF2E Kinv(NTL::INIT_SIZE, e, e);
  for (long j=0; j<e; j++)
    conv(Kinv[0][j], NTL::GF2X(j,1)); // Kinv[0][j] = X^j
  for (long i=1; i<e; i++) for (long j=0; j<e; j++) {
    power(Kinv[i][j], Kinv[0][j], 1L<<(8*i)); // (X^j)^{2^{8*i}}
  }
  NTL::mat_GF2E K(NTL::INIT_SIZE, e, e);
  inv(K, Kinv); // invert Kinv to get K

  // Encode K in slots
  unpacking.SetDims(e,e);
  for (long i=0; i<e; i++) for (long j=0; j<e; j++) {
    std::vector<NTL::GF2X> slots(ea.size(), rep(K[i][j])); // K[i][j] in all the slots
    NTL::ZZX tmp; ea.encode(tmp, slots);
    NTL::conv(unpacking[i][j], tmp);
  }
}
void packCtxt(std::vector<helib::Ctxt>& to, const std::vector<helib::Ctxt>& from,
		     const NTL::GF2X& XinSlots)
{
  if (from.size() <= 1) { // nothing to do here
    to = from; return;
  }

  // Get the context and the ea for "fully packed" polynomials
  const helib::Context& context = from[0].getContext();
  const helib::EncryptedArrayDerived<helib::PA_GF2>& ea = context.ea->getDerived(helib::PA_GF2());
  const NTL::GF2XModulus& PhimX = ea.getTab().getPhimXMod();
  long e = ea.getDegree() / 8; // the extension degree
  long nPacked = helib::divc(from.size(), e); // How many fully-packed ciphertexts

  // Initialize the vector 'to' with empty cipehrtexts
  to.assign(nPacked, helib::Ctxt(helib::ZeroCtxtLike, from[0]));

  // Each ctxt in 'to' is the result of packing <= e ctxts from 'from'
  for (long i=0; i<(long) to.size(); i++) {
    to[i] = from[e*i];
    if (e*i == (long)from.size()-1) break; // check if we are done packing

    helib::Ctxt tmp = from[e*i +1];
    tmp.multByConstant(NTL::conv<NTL::ZZX>(XinSlots));
    to[i] += tmp;
    if (e*i == (long)from.size()-2) break; // check if we are done packing

    NTL::GF2X X2i = XinSlots; // X^i, initially i=1
    for (long j= e*i +2; j<e*(i+1) && j<(long)from.size(); j++) {
      MulMod(X2i, X2i, XinSlots, PhimX);  // X^i
      tmp = from[j];
      tmp.multByConstant(NTL::conv<NTL::ZZX>(X2i));
      to[i] += tmp;
    }
  }
}
void unpackCtxt(std::vector<helib::Ctxt>& to, const std::vector<helib::Ctxt>& from,
		      const NTL::Mat<NTL::GF2X>& unpackConsts)
{
  // Get the context and the ea for "fully packed" polynomials
  const helib::Context& context = from[0].getContext();
  const helib::EncryptedArrayDerived<helib::PA_GF2>& ea = context.ea->getDerived(helib::PA_GF2());
  long e = ea.getDegree() / 8; // the extension degree
  long nUnpacked = from.size()*e; // How many lightly-packed ciphertexts
  if (to.size()==0) to.resize(nUnpacked, helib::Ctxt(helib::ZeroCtxtLike, from[0]));
  else {
    if (nUnpacked > (long) to.size()) nUnpacked = to.size();
    for (long i=0; i<(long)to.size(); i++) to[i].clear();
  }
  // At this point 'to' contains empty (zero) ciphertexts

  long nPacked = helib::divc(nUnpacked, 8);
  for (long idx=0; idx<nPacked; idx++) {
    std::vector<helib::Ctxt> conjugates(e, from[idx]); // Compute the conjugates, Z^{2^{8j}}
    for (long j=1; j<e; j++)
      conjugates[j].frobeniusAutomorph(8*j);

    for (long i=0; i<e && (idx*e +i)<(long)to.size(); i++) {
      // Recall that to[idx*e +i] was initialize to zero
      for (long j=0; j<e; j++) {
        helib::Ctxt tmp = conjugates[j];
        tmp.multByConstant(NTL::conv<NTL::ZZX>(unpackConsts[i][j]));
        to[idx*e +i] += tmp;
      }
    }
  }
}
void batchRecrypt(helib::Ctxt& ctxt, 
            const helib::PubKey& public_key, 
            helib::SecKey& secret_key,
            helib::EncryptedArrayDerived<helib::PA_GF2>& ea2,
            int groupnum) {
  const helib::PubKey& pubkey = ctxt.getPubKey();
  pubkey.reCrypt(ctxt);
}

void oneRound(helib::Ctxt& ctxt, helib::EncryptedArrayDerived<helib::PA_GF2>& ea2, 
    helib::SecKey& secret_key, 
    int round, 
    int slots,
    const std::vector<helib::Ctxt>& expandEncKeys,
    const std::vector<PolyType>& affMat1,
    const std::vector<PolyType>& affMat2,
    const PolyType& affVec1,
    const PolyType& affVec2,
    const std::vector<PolyType>& lccMat1,
    const std::vector<PolyType>& lccMat2,
    const std::vector<PolyType>& lccMat3,
    const PolyType& encSelector,
    const PolyType& encSelector1,
    const PolyType& encSelector2,
    const PolyType& encSelector3,
    const PolyType& encSelector4,
    const PolyType& encSelector5,
    const helib::PubKey& public_key,
    int groupnum,
    const PolyType& mVec1,
    const PolyType& mVec2,
    const PolyType& mVec3,
    const helib::EncryptedArray& ea,
    const helib::PermNetwork& net,
    const helib::PermNetwork& net1,
    const helib::PermNetwork& net2
    ) {
  helib::Ctxt ctxt0(ctxt), ctxt4(ctxt), ctxt8(ctxt), ctxt12(ctxt), tmpctxt(ctxt);
  ea2.rotate1D(ctxt4, 0, 4);
  ea2.rotate1D(ctxt8, 0, 8);
  ea2.rotate1D(ctxt12, 0, 12);

  ctxt4.cleanUp();
  ctxt8.cleanUp();
  ctxt12.cleanUp();

  ctxt0.addCtxt(ctxt4);
  ctxt0.addCtxt(ctxt8);
  ctxt0.addCtxt(expandEncKeys[round]);

  applyLinPolyLL(ctxt0, affMat1, ea2.getDegree());
  ctxt0.addConstant(affVec1);
  invertSingle(ctxt0);

  helib::Ctxt ctxtaf1(ctxt0), ctxtaf2(ctxt0), ctxtaf3(ctxt0);
  applyLinPolyLL(ctxtaf1, lccMat1, ea2.getDegree());
  applyLinPolyLL(ctxtaf2, lccMat2, ea2.getDegree());
  applyLinPolyLL(ctxtaf3, lccMat3, ea2.getDegree());
  ctxtaf1.addConstant(mVec1);
  ctxtaf2.addConstant(mVec2);
  ctxtaf3.addConstant(mVec3);

  helib::Ctxt ctxtaf20(ctxtaf2), ctxtaf21(ctxtaf2);
  net.applyToCtxt(ctxtaf20, ea);
  net1.applyToCtxt(ctxtaf21, ea);
  net2.applyToCtxt(ctxtaf3, ea);

  ctxtaf1.addCtxt(ctxtaf20);
  ctxtaf1.addCtxt(ctxtaf21);
  ctxtaf1.addCtxt(ctxtaf3);
  ctxtaf1.multByConstant(encSelector);

  ctxtaf1.addCtxt(ctxt12);
  ctxt = ctxtaf1;
  ctxt.cleanUp();
}

int main(int argc, char* argv[])
{
  auto start = std::chrono::system_clock::now();
  std::time_t start_time = std::chrono::system_clock::to_time_t(start);
  std::cout << "##begin:" << std::ctime(&start_time) << std::endl;

  long mValues[][14] = { 
//{ p, phi(m),  m,   d, m1, m2, m3,   g1,    g2,   g3,ord1,ord2,ord3, c_m}
  { 2, 46080, 53261, 24, 17,13, 241, 43863,28680,15913, 16, 12,-10, 100}, // m=13*17*(241) m/phim(m)=1.15   C=69  D=4 E=3
};

  int cid = 0;
  // Plaintext prime modulus
  unsigned long p = mValues[cid][0];
  // Cyclotomic polynomial - defines phi(m)
  unsigned long m = mValues[cid][2];
  // Hensel lifting (default = 1)
  unsigned long r = 1;
  // Number of bits of the modulus chain
  // unsigned long bits = 2400;
  // unsigned long bits = 3000;
  unsigned long bits = 1000;
  // Number of columns of Key-Switching matrix (default = 2 or 3)
  unsigned long c = 3;

  bool boot = true;
  bool packed = true;

  std::vector<long> gens;
  std::vector<long> ords;
  NTL::Vec<long> mvec;
  gens.push_back(mValues[cid][7]);
  if (mValues[cid][8]>1)   gens.push_back(mValues[cid][8]);
  if (mValues[cid][9]>1) gens.push_back(mValues[cid][9]);

  ords.push_back(mValues[cid][10]);
  if (abs(mValues[cid][11])>1) ords.push_back(mValues[cid][11]);
  if (abs(mValues[cid][12])>1) ords.push_back(mValues[cid][12]);
  // ords.push_back(-16);

  if (boot) {
    if (cid == 11) {
      mvec.append(5);
      mvec.append(13);
      mvec.append(17);
      mvec.append(241);
    } else {
      mvec.append(mValues[cid][4]);
      if (mValues[cid][5]>1) mvec.append(mValues[cid][5]);
      if (mValues[cid][6]>1) mvec.append(mValues[cid][6]);
    }
  }
  long e = mValues[cid][3] /8;

  std::cout << "Initialising context object..." << std::endl;
  // Initialize context
  helib::Context context(m, p, r, gens, ords);
  // context.bitsPerLevel = 23;
  context.zMStar.set_cM(mValues[cid][13]/100.0);
  // Modify the context, adding primes to the modulus chain
  std::cout << "Building modulus chain..." << std::endl;
  buildModChain(context, bits, c, true, 64);
  if (boot) context.makeBootstrappable(mvec, 64);

  std::cout << "security=" << context.securityLevel() << std::endl;
  std::cout << "# small primes = " << context.smallPrimes.card() << "\n";
  std::cout << "# ctxt primes = " << context.ctxtPrimes.card() << "\n";
  std::cout << "# bits in ctxt primes = "
            << long(context.logOfProduct(context.ctxtPrimes) / log(2.0) + 0.5)
            << "\n";
  std::cout << "# special primes = " << context.specialPrimes.card() << "\n";
  std::cout << "# bits in special primes = "
            << long(context.logOfProduct(context.specialPrimes) / log(2.0) +
                    0.5)
            << "\n";
  std::cout << "scale=" << context.scale << std::endl;
  std::cout << std::endl;

    // Print the security level
  std::cout << "Security: " << context.securityLevel() << std::endl;

  // Secret key management
  std::cout << "Creating secret key..." << std::endl;
  // Create a secret key associated with the context
  helib::SecKey secret_key(context);
  // Generate the secret key
  secret_key.GenSecKey(64);

  std::cout << "Generating key-switching matrices..." << std::endl;
  // Compute key-switching matrices that we need
    // Add key-switching matrices for the automorphisms that we need
  long ord = context.zMStar.OrderOf(0);
  for (long i = 1; i < 16; i++) { // rotation along 1st dim by size i*ord/16
    long exp = i*ord/16;
    long val = NTL::PowerMod(context.zMStar.ZmStarGen(0), exp, m); // val = g^exp

    // From s(X^val) to s(X)
    secret_key.GenKeySWmatrix(1, val);
    if (!context.zMStar.SameOrd(0))
      // also from s(X^{1/val}) to s(X)
      secret_key.GenKeySWmatrix(1, NTL::InvMod(val,m));
  }

  helib::addFrbMatrices(secret_key);      // Also add Frobenius key-switching
  helib::addSome1DMatrices(secret_key);
  if (boot) {
    secret_key.genRecryptData();
  }

  const helib::PubKey& public_key = secret_key;

  // Get the EncryptedArray of the context
  const uint8_t sm4PolyBytes[] = { 0xf5, 0x1 }; // X^8+X^7+X^6+X^5+X^4+X^2+1
  const NTL::GF2X sm4Poly = NTL::GF2XFromBytes(sm4PolyBytes, 2);
  helib::EncryptedArrayDerived<helib::PA_GF2> ea2(context, sm4Poly, context.alMod);

  // Get the number of slot (phi(m))
  long nslots = ea2.size();
  int groupnum = nslots/16;
  long blocknum;
  if (boot && packed) {
    blocknum = groupnum * e;
  } else {
    blocknum = groupnum;
  }
  long ctxtnum = blocknum / groupnum;

  std::cout << "Number of slots: " << nslots << std::endl;
  std::cout << "ea degree: " << ea2.getDegree() << std::endl;
  std::cout << "group num:" << groupnum << std::endl;
  std::cout << "block num:" << blocknum << std::endl;
  std::cout << "ctxt num:" << ctxtnum << std::endl;


  std::vector<NTL::ZZX> encData(ctxtnum, NTL::ZZX::zero());
  // Create a vector of long with nslots elements
  std::vector<NTL::GF2X> slots(ea2.size(), NTL::GF2X::zero());
  std::vector<helib::Ctxt> ctxts(ctxtnum, helib::Ctxt(public_key));
  // unsigned char b[16] = { 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10};
  unsigned char b[16] = { 0x68, 0x1e, 0xdf, 0x34, 0xd2, 0x06, 0x96, 0x5e, 0x86, 0xb3, 0xe9, 0x4f, 0x53, 0x6e, 0x42, 0x46};

  for (int n = 0; n < ctxtnum; n++) {
    // slots.clear();
    for (int i = 0; i < 16; i++) {
      for (int j = 0; j < groupnum; j++) {
        unsigned char tmpb = b[i];
        NTL::GF2XFromBytes(slots[i*groupnum+j], &tmpb, 1);
      }
    }

    ea2.encode(encData[n], slots);
    public_key.Encrypt(ctxts[n], encData[n]);
  }

  sm4_context octx;
  unsigned char key[16] = { 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10};
  unsigned char out[16];
  sm4_setkey_dec(&octx, key);
  sm4_crypt_ecb(&octx, SM4_DECRYPT, 16, b, out);


  // const helib::PubKey& public_key = secret_key;
  helib::Ctxt tmpCtxt(public_key);
  std::vector<helib::Ctxt> expandEncKeys(32, tmpCtxt);
  for (int i = 0; i < 32; i++) {
    unsigned long curkey = octx.sk[i];
    unsigned char curkeypart1 = (curkey >> 24) & 0xff;
    unsigned char curkeypart2 = (curkey >> 16) & 0xff;
    unsigned char curkeypart3 = (curkey >> 8) & 0xff;
    unsigned char curkeypart4 = curkey & 0xff;

    std::vector<NTL::GF2X> keySlots(ea2.size(), NTL::GF2X::zero());
    for (int j = 12; j < 16; j++) {
      for (int k = 0; k < groupnum; k++) {
        if (j == 12) {
          NTL::GF2XFromBytes(keySlots[j*groupnum+k], &curkeypart1, 1);
        } else if (j == 13) {
          NTL::GF2XFromBytes(keySlots[j*groupnum+k], &curkeypart2, 1);
        } else if (j == 14) {
          NTL::GF2XFromBytes(keySlots[j*groupnum+k], &curkeypart3, 1);
        } else if (j == 15) {
          NTL::GF2XFromBytes(keySlots[j*groupnum+k], &curkeypart4, 1);
        }
      }
    }
    NTL::ZZX curEncodeKey;
    ea2.encode(curEncodeKey, keySlots);
    public_key.Encrypt(expandEncKeys[i], curEncodeKey);
  }
  std::vector<NTL::GF2X> selectorSlots(ea2.size(), NTL::GF2X::zero());
  std::vector<NTL::GF2X> selectorSlots1(ea2.size(), NTL::GF2X::zero());
  std::vector<NTL::GF2X> selectorSlots2(ea2.size(), NTL::GF2X::zero());
  std::vector<NTL::GF2X> selectorSlots3(ea2.size(), NTL::GF2X::zero());
  std::vector<NTL::GF2X> selectorSlots4(ea2.size(), NTL::GF2X::zero());
  std::vector<NTL::GF2X> selectorSlots5(ea2.size(), NTL::GF2X::zero());
  std::vector<NTL::GF2X> selectorSlots6(ea2.size(), NTL::GF2X::zero());
  std::vector<NTL::GF2X> selectorSlots7(ea2.size(), NTL::GF2X::zero());
  std::vector<NTL::GF2X> selectorSlots8(ea2.size(), NTL::GF2X::zero());
  unsigned char selectorchar[1] = { 0x01 };
  for (int i = 12*groupnum; i < nslots; i++) {
    NTL::GF2XFromBytes(selectorSlots[i], &selectorchar[0], 1);
  }
  for (int i = 12*groupnum; i < 13*groupnum; i++) {
    NTL::GF2XFromBytes(selectorSlots1[i], &selectorchar[0], 1);
  }
  for (int i = 13*groupnum; i < 14*groupnum; i++) {
    NTL::GF2XFromBytes(selectorSlots2[i], &selectorchar[0], 1);
  }
  for (int i = 14*groupnum; i < 15*groupnum; i++) {
    NTL::GF2XFromBytes(selectorSlots3[i], &selectorchar[0], 1);
  }
  for (int i = 15*groupnum; i < nslots; i++) {
    NTL::GF2XFromBytes(selectorSlots4[i], &selectorchar[0], 1);
  }
  for (int i = 0; i < 12*groupnum; i++) {
    NTL::GF2XFromBytes(selectorSlots5[i], &selectorchar[0], 1);
  }
  for (int i = 0; i < 4*groupnum; i++) {
    NTL::GF2XFromBytes(selectorSlots6[i], &selectorchar[0], 1);
  }
  for (int i = 4*groupnum; i < 8*groupnum; i++) {
    NTL::GF2XFromBytes(selectorSlots7[i], &selectorchar[0], 1);
  }
  for (int i = 8*groupnum; i < 12*groupnum; i++) {
    NTL::GF2XFromBytes(selectorSlots8[i], &selectorchar[0], 1);
  }
  NTL::ZZX tmpEncSelector, tmpEncSelector1, tmpEncSelector2, tmpEncSelector3, tmpEncSelector4, tmpEncSelector5,
    tmpEncSelector6, tmpEncSelector7, tmpEncSelector8;
  ea2.encode(tmpEncSelector, selectorSlots);
  ea2.encode(tmpEncSelector1, selectorSlots1);
  ea2.encode(tmpEncSelector2, selectorSlots2);
  ea2.encode(tmpEncSelector3, selectorSlots3);
  ea2.encode(tmpEncSelector4, selectorSlots4);
  ea2.encode(tmpEncSelector5, selectorSlots5);
  ea2.encode(tmpEncSelector6, selectorSlots6);
  ea2.encode(tmpEncSelector7, selectorSlots7);
  ea2.encode(tmpEncSelector8, selectorSlots8);

  PolyType encSelector(tmpEncSelector, context, context.ctxtPrimes | context.specialPrimes);
  PolyType encSelector1(tmpEncSelector1, context, context.ctxtPrimes | context.specialPrimes);
  PolyType encSelector2(tmpEncSelector2, context, context.ctxtPrimes | context.specialPrimes);
  PolyType encSelector3(tmpEncSelector3, context, context.ctxtPrimes | context.specialPrimes);
  PolyType encSelector4(tmpEncSelector4, context, context.ctxtPrimes | context.specialPrimes);
  PolyType encSelector5(tmpEncSelector5, context, context.ctxtPrimes | context.specialPrimes);
  PolyType encSelector6(tmpEncSelector6, context, context.ctxtPrimes | context.specialPrimes);
  PolyType encSelector7(tmpEncSelector7, context, context.ctxtPrimes | context.specialPrimes);
  PolyType encSelector8(tmpEncSelector8, context, context.ctxtPrimes | context.specialPrimes);
  unsigned char cc[] = { 203, 151, 47, 94, 188, 121, 242, 229, 211};
  unsigned char cc1[] = { 203, 151, 47, 94, 188, 121, 242, 229, 211};
  std::vector<PolyType> affMat1, affMat2;
  PolyType affVec1(context, context.ctxtPrimes | context.specialPrimes), affVec2(context, context.ctxtPrimes | context.specialPrimes);
  buildAffine(affMat1, &affVec1, cc, ea2);
  buildAffine(affMat2, &affVec2, cc1, ea2);

  unsigned char ttcc1[] = {0xe7, 0xcb, 0x93, 0x26, 0x4c, 0x9d, 0x3a, 0x71, 0x9f };
  unsigned char ttcc2[] = {0x2f, 0x5e, 0xbc, 0x79, 0xf2, 0xe5, 0xcb, 0x97, 0x4f };
  unsigned char ttcc3[] = {0xc8, 0x95, 0x2f, 0x5f, 0xbe, 0x78, 0xf1, 0xe6, 0xd0 };
  std::vector<PolyType> lccMat1, lccMat2, lccMat3;
  PolyType mVec1(context, context.ctxtPrimes | context.specialPrimes);
  PolyType mVec2(context, context.ctxtPrimes | context.specialPrimes);
  PolyType mVec3(context, context.ctxtPrimes | context.specialPrimes);
  buildAffine(lccMat1, &mVec1, ttcc1, ea2);
  buildAffine(lccMat2, &mVec2, ttcc2, ea2);
  buildAffine(lccMat3, &mVec3, ttcc3, ea2);
 

  NTL::ZZX G = context.alMod.getFactorsOverZZ()[0];
  helib::EncryptedArray ea(context, G);

  NTL::GF2X XinSlots; // "Fully packed" poly with X in all the slots, for packing
  NTL::Mat<NTL::GF2X> unpacking; // constants for unpacking after recryption
  setPackingConstants(XinSlots, unpacking, ea2);

  NTL::Vec<helib::GenDescriptor> vec(NTL::INIT_SIZE, ea.dimension());
  for (long i = 0; i < ea.dimension(); i++)
    vec[i] = helib::GenDescriptor(/*order=*/ea.sizeOfDimension(i),
                                  /*good=*/ea.nativeDimension(i),
                                  /*genIdx=*/i);
  long widthBound = 1 + log2((double)ea2.size());
  helib::GeneratorTrees trees;
  long cost = trees.buildOptimalTrees(vec, widthBound);

  helib::Permut pi;
  pi.SetLength(trees.getSize());
  for (int i = 0; i < trees.getSize(); i++) {
    if ( i < 1440) {
      pi[i] = i;
    } else if (i >= 1440 && i<1800) {
      pi[i] = i+120;
    } else if (i >= 1800) {
      pi[i] = i-360;
    }
  }
  std::cout << std::endl;
  // Build a permutation network for pi
  helib::PermNetwork net;
  net.buildNetwork(pi, trees);
  // make sure we have the key-switching matrices needed for this network
  helib::addMatrices4Network(secret_key, net);

  helib::Permut pi1;
  pi1.SetLength(trees.getSize());
  // helib::randomPerm(pi, trees.getSize());
  for (int i = 0; i < trees.getSize(); i++) {
    if ( i < 1440) {
      pi1[i] = i;
    } else if (i >= 1440 && i<1680) {
      pi1[i] = i+240;
    } else if (i >= 1680) {
      pi1[i] = i-240;
    }
  }
  std::cout << std::endl;
  // Build a permutation network for pi
  helib::PermNetwork net1;
  net1.buildNetwork(pi1, trees);
  // make sure we have the key-switching matrices needed for this network
  helib::addMatrices4Network(secret_key, net1);

  helib::Permut pi2;
  pi2.SetLength(trees.getSize());

  for (int i = 0; i < trees.getSize(); i++) {
    if ( i < 1440) {
      pi2[i] = i;
    } else if (i >= 1440 && i<1560) {
      pi2[i] = i+360;
    } else if (i >= 1560) {
      pi2[i] = i-120;
    }
  }
  std::cout << std::endl;
  // Build a permutation network for pi
  helib::PermNetwork net2;
  net2.buildNetwork(pi2, trees);
  // make sure we have the key-switching matrices needed for this network
  helib::addMatrices4Network(secret_key, net2);

  for (int i = 0; i < 32; i++) {
    std::cout << "round:" << i << ":" << ctxts[0].capacity() << ":" << ctxts[0].getPrimeSet().card() << std::endl;
    for (int n = 0; n < ctxtnum; n++) {
        std::cout << "ctxt num:" << n << std::endl;
        oneRound(ctxts[n], 
                  ea2, 
                  secret_key, 
                  i, 
                  nslots, 
                  expandEncKeys, 
                  affMat1, 
                  affMat2, 
                  affVec1, 
                  affVec2, 
                  lccMat1, 
                  lccMat2, 
                  lccMat3,
                  encSelector,
                  encSelector1,
                  encSelector2,
                  encSelector3,
                  encSelector4,
                  encSelector5,
                  public_key,
                  groupnum,
                  mVec1,
                  mVec2,
                  mVec3,
                  ea,
                  net,
                  net1,
                  net2
                  );
          if (i == 31) {
            //last round, reverse
            std::cout << "##last round, reverse" << std::endl;
            helib::Ctxt ctxt1(ctxts[n]), ctxt2(ctxts[n]), ctxt3(ctxts[n]), ctxt4(ctxts[n]);
            ctxt1.multByConstant(encSelector);
            ctxt2.multByConstant(encSelector6);
            ctxt3.multByConstant(encSelector7);
            ctxt4.multByConstant(encSelector8);
            ea2.rotate1D(ctxt1, 0, 4);
            ea2.rotate1D(ctxt2, 0, 12);
            ea2.rotate1D(ctxt3, 0, 4);
            ea2.rotate1D(ctxt4, 0, 12);
            ctxt1.addCtxt(ctxt2);
            ctxt1.addCtxt(ctxt3);
            ctxt1.addCtxt(ctxt4);

            NTL::ZZX new_plaintext_result1;
            secret_key.Decrypt(new_plaintext_result1, ctxt1);
            std::cout << "result:" << std::endl;
            std::vector<NTL::GF2X> res2b;
            ea2.decode(res2b, new_plaintext_result1);
            for (int i = 0; i < res2b.size(); i++) {
              unsigned char b;
              NTL::BytesFromGF2X(&b, res2b[i], 1);
              std::cout << std::hex << (int)b << " ";
              if ((i+1) % groupnum == 0) {
                std::cout << std::endl;
              }
            }
          }
    }
    if ((i == 8 || i == 14 || i == 20 ||
      i == 26) && boot) {
      // batchRecrypt(ctxts[0], public_key, secret_key, ea2, groupnum);
      if (ctxtnum > 1) {
        std::vector<helib::Ctxt> ct(ctxtnum/e, helib::Ctxt(public_key));
        packCtxt(ct, ctxts, XinSlots);
        batchRecrypt(ct[0], public_key, secret_key, ea2, groupnum);
        unpackCtxt(ctxts, ct, unpacking);
      } else {
        batchRecrypt(ctxts[0], public_key, secret_key, ea2, groupnum);
      }
    } 
  }

  auto end = std::chrono::system_clock::now();
  std::time_t end_time = std::chrono::system_clock::to_time_t(end);
  std::cout << "##end:" << std::ctime(&end_time) << std::endl;
  std::cout << "##from " << std::ctime(&start_time) << " to " << std::ctime(&end_time) << std::endl;

}