#include <iostream>

#include <helib/helib.h>
#include "originsm4.h"

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
void buildAffine(std::vector<NTL::ZZX>& binMat, NTL::ZZX* binVec,
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
  std::vector<NTL::ZZX>& zzxMat=binMat;
  zzxMat.resize(8);
  scratch.resize(ea2.size());
  for (long j = 0; j < 8; j++) {
    for (long i = 0; i < ea2.size(); i++) // set all slots to C[j]
      scratch[i] = C[j];
    ea2.encode(zzxMat[j], scratch);       // encode these slots
  }

  if (binVec != NULL) {
    NTL::GF2X cc8;
    GF2XFromBytes(cc8, &cc[8], 1);
    for (long i = 0; i < ea2.size(); i++)  // set all slots to cc8
      scratch[i] = cc8;
    ea2.encode(*binVec, scratch);       // encode these slots
  }
}
void oneRound(helib::Ctxt& ctxt, helib::EncryptedArrayDerived<helib::PA_GF2>& ea2, 
    helib::SecKey& secret_key, 
    int round, 
    int slots,
    const std::vector<helib::Ctxt>& expandEncKeys,
    const std::vector<NTL::ZZX>& affMat1,
    const std::vector<NTL::ZZX>& affMat2,
    const NTL::ZZX& affVec1,
    const NTL::ZZX& affVec2,
    const std::vector<NTL::ZZX>& lccMat1,
    const std::vector<NTL::ZZX>& lccMat2,
    const std::vector<NTL::ZZX>& lccMat3,
    const NTL::ZZX& encSelector,
    const NTL::ZZX& encSelector1,
    const NTL::ZZX& encSelector2,
    const NTL::ZZX& encSelector3,
    const NTL::ZZX& encSelector4,
    const NTL::ZZX& encSelector5
    ) {
  helib::Ctxt ctxt0(ctxt), ctxt4(ctxt), ctxt8(ctxt), ctxt12(ctxt);
  ea2.rotate1D(ctxt4, 0, 4);
  ea2.rotate1D(ctxt8, 0, 8);
  ea2.rotate1D(ctxt12, 0, 12);

  ctxt4.cleanUp();
  ctxt8.cleanUp();
  ctxt12.cleanUp();

  ctxt0.addCtxt(ctxt4);
  ctxt0.addCtxt(ctxt8);
  // ctxt0.addCtxt(ctxt12);

  int groupnum = slots/16;
  ctxt0.multByConstant(encSelector);
  ctxt0.addCtxt(expandEncKeys[round]);

  applyLinPolyLL(ctxt0, affMat1, ea2.getDegree());
  ctxt0.addConstant(affVec1);
  invertSingle(ctxt0);
  applyLinPolyLL(ctxt0, affMat2, ea2.getDegree());
  ctxt0.addConstant(affVec2);

  helib::Ctxt ctxtaf1(ctxt0), ctxtaf2(ctxt0), ctxtaf3(ctxt0);
  applyLinPolyLL(ctxtaf1, lccMat1, ea2.getDegree());
  applyLinPolyLL(ctxtaf2, lccMat2, ea2.getDegree());
  applyLinPolyLL(ctxtaf3, lccMat3, ea2.getDegree());

  helib::Ctxt ctxtaf2_15(ctxtaf2), ctxtaf2_14(ctxtaf2), ctxtaf2_2(ctxtaf2), ctxtaf2_3(ctxtaf2);
  ea2.rotate1D(ctxtaf2_15, 0, 15);
  ea2.rotate1D(ctxtaf2_14, 0, 14);
  ea2.rotate1D(ctxtaf2_2, 0, 2);
  ea2.rotate1D(ctxtaf2_3, 0, 3);

  helib::Ctxt ctxtaf3_13(ctxtaf3), ctxtaf3_1(ctxtaf3);
  ea2.rotate1D(ctxtaf3_13, 0, 13);
  ea2.rotate1D(ctxtaf3_1, 0, 1);

  ctxtaf2_15.cleanUp();
  ctxtaf2_14.cleanUp();
  ctxtaf2_2.cleanUp();
  ctxtaf2_3.cleanUp();
  ctxtaf3_13.cleanUp();
  ctxtaf3_1.cleanUp();

  helib::Ctxt ctxtaf1_1(ctxtaf1), ctxtaf1_2(ctxtaf1), ctxtaf1_3(ctxtaf1), ctxtaf1_4(ctxtaf1);
  ctxtaf1_1.addCtxt(ctxtaf2_15);
  ctxtaf1_1.addCtxt(ctxtaf2_14);
  ctxtaf1_1.addCtxt(ctxtaf3_13);

  ctxtaf1_2.addCtxt(ctxtaf3_1);
  ctxtaf1_2.addCtxt(ctxtaf2_15);
  ctxtaf1_2.addCtxt(ctxtaf2_14);

  ctxtaf1_3.addCtxt(ctxtaf2_2);
  ctxtaf1_3.addCtxt(ctxtaf3_1);
  ctxtaf1_3.addCtxt(ctxtaf2_15);

  ctxtaf1_4.addCtxt(ctxtaf2_3);
  ctxtaf1_4.addCtxt(ctxtaf2_2);
  ctxtaf1_4.addCtxt(ctxtaf3_1);

  ctxtaf1_1.multByConstant(encSelector1);
  ctxtaf1_2.multByConstant(encSelector2);
  ctxtaf1_3.multByConstant(encSelector3);
  ctxtaf1_4.multByConstant(encSelector4);

  ctxtaf1_1.addCtxt(ctxtaf1_2);
  ctxtaf1_1.addCtxt(ctxtaf1_3);
  ctxtaf1_1.addCtxt(ctxtaf1_4);

  ctxtaf1_1.addCtxt(ctxt12);
  ctxtaf1_1.multByConstant(encSelector);

  ea2.rotate1D(ctxt, 0, 12);
  ctxt.cleanUp();
  ctxt.multByConstant(encSelector5);
  ctxt.addCtxt(ctxtaf1_1);
}

int main(int argc, char* argv[])
{
  auto start = std::chrono::system_clock::now();
  std::time_t start_time = std::chrono::system_clock::to_time_t(start);
  std::cout << "##begin:" << std::ctime(&start_time) << std::endl;

  long mValues[][14] = { 
//{ p, phi(m),  m,   d, m1, m2, m3,   g1,    g2,   g3,ord1,ord2,ord3, c_m}
 { 2, 184320, 266305, 24, 0, 0, 0, 177, 7, 2891, 16, 120, 4, 100}, //bits=3800, 30rounds, //bits=40000, 31.5 rounds //bits=4200, 32rounds, but securitylevel about 120.8
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
  unsigned long bits = 4100;
  // Number of columns of Key-Switching matrix (default = 2 or 3)
  unsigned long c = 3;

  bool boot = false;

  std::vector<long> gens;
  std::vector<long> ords;
  gens.push_back(mValues[cid][7]);
  if (mValues[cid][8]>1)   gens.push_back(mValues[cid][8]);
  if (mValues[cid][9]>1) gens.push_back(mValues[cid][9]);

  ords.push_back(mValues[cid][10]);
  if (abs(mValues[cid][11])>1) ords.push_back(mValues[cid][11]);
  if (abs(mValues[cid][12])>1) ords.push_back(mValues[cid][12]);

  std::cout << "Initialising context object..." << std::endl;
  // Initialize context
  helib::Context context(m, p, r, gens, ords);
  // context.bitsPerLevel = 23;
  context.zMStar.set_cM(mValues[cid][13]/100.0);
  // Modify the context, adding primes to the modulus chain
  std::cout << "Building modulus chain..." << std::endl;
  buildModChain(context, bits, c);
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

  // Public key management
  // Set the secret key (upcast: SecKey is a subclass of PubKey)
  const helib::PubKey& public_key = secret_key;

  // Get the EncryptedArray of the context
//   const helib::EncryptedArray& ea = *(context.ea);
  const uint8_t sm4PolyBytes[] = { 0xf5, 0x1 }; // X^8+X^7+X^6+X^5+X^4+X^2+1
  const NTL::GF2X sm4Poly = NTL::GF2XFromBytes(sm4PolyBytes, 2);
  helib::EncryptedArrayDerived<helib::PA_GF2> ea2(context, sm4Poly, context.alMod);

  // Get the number of slot (phi(m))
  long nslots = ea2.size();
  int groupnum = nslots/16;
  std::cout << "Number of slots: " << nslots << std::endl;
  std::cout << "ea degree: " << ea2.getDegree() << std::endl;
  std::cout << "group num:" << groupnum << std::endl;

  // Create a vector of long with nslots elements
  std::vector<NTL::GF2X> slots(ea2.size(), NTL::GF2X::zero());
  // unsigned char b[16] = { 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10};
  unsigned char b[16] = { 0x68, 0x1e, 0xdf, 0x34, 0xd2, 0x06, 0x96, 0x5e, 0x86, 0xb3, 0xe9, 0x4f, 0x53, 0x6e, 0x42, 0x46};


  for (int i = 0; i < 16; i++) {
    for (int j = 0; j < groupnum; j++) {
      unsigned char tmpb = b[i];
      NTL::GF2XFromBytes(slots[i*groupnum+j], &tmpb, 1);
    }
  }

  NTL::ZZX encData;
  ea2.encode(encData, slots);
  helib::Ctxt ctxt(public_key);
  public_key.Encrypt(ctxt, encData);

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
  // int groupnum = nslots/16;
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
  NTL::ZZX encSelector, encSelector1, encSelector2, encSelector3, encSelector4, encSelector5,
    encSelector6, encSelector7, encSelector8;
  ea2.encode(encSelector, selectorSlots);
  ea2.encode(encSelector1, selectorSlots1);
  ea2.encode(encSelector2, selectorSlots2);
  ea2.encode(encSelector3, selectorSlots3);
  ea2.encode(encSelector4, selectorSlots4);
  ea2.encode(encSelector5, selectorSlots5);
  ea2.encode(encSelector6, selectorSlots6);
  ea2.encode(encSelector7, selectorSlots7);
  ea2.encode(encSelector8, selectorSlots8);
  unsigned char cc[] = { 203, 151, 47, 94, 188, 121, 242, 229, 211};
  unsigned char cc1[] = { 203, 151, 47, 94, 188, 121, 242, 229, 211};
  std::vector<NTL::ZZX> affMat1, affMat2;
  NTL::ZZX affVec1, affVec2;
  buildAffine(affMat1, &affVec1, cc, ea2);
  buildAffine(affMat2, &affVec2, cc1, ea2);

  unsigned char lcc1[] = { 0x05, 0x0a, 0x14, 0x28, 0x50, 0xa0, 0x40, 0x80};
  unsigned char lcc2[] = { 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x01, 0x02};
  unsigned char lcc3[] = { 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x41, 0x82};

  std::vector<NTL::ZZX> lccMat1, lccMat2, lccMat3;
  buildAffine(lccMat1, NULL, lcc1, ea2);
  buildAffine(lccMat2, NULL, lcc2, ea2);
  buildAffine(lccMat3, NULL, lcc3, ea2);

  for (int i = 0; i < 32; i++) {
    std::cout << "##round " << i << ":" << std::endl;
    oneRound(ctxt, 
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
              encSelector5);

    if (i == 31) {
      //last round, reverse
      std::cout << "##last round, reverse" << std::endl;
      helib::Ctxt ctxt1(ctxt), ctxt2(ctxt), ctxt3(ctxt), ctxt4(ctxt);
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
  
  auto end = std::chrono::system_clock::now();
  std::time_t end_time = std::chrono::system_clock::to_time_t(end);
  std::cout << "##end:" << std::ctime(&end_time) << std::endl;
  std::cout << "##from " << std::ctime(&start_time) << " to " << std::ctime(&end_time) << std::endl;
}